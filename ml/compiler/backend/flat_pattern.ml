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

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/pattern_matching/pattern_comp.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;


let flat_pattern_config_FIELDS = define_record "flat_pattern_config"
  ["pat_heuristic","num"];;

let init_config_def = cake_define
  `flat_pattern_init_config ph = mk_flat_pattern_config ph`;;
hol4_overload "init_config" "flat_pattern_init_config";;

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

let compile_pat_bindings_def = cake_define_list
  [`compile_pat_bindings _1 _2 [] exp = (LN,exp)`;
   `compile_pat_bindings t i ((Pany,_3,_4) :: m) exp =
      compile_pat_bindings t i m exp`;
   `compile_pat_bindings t i (((Pvar s:pattern_semantics_pat),k,x) :: m)
  exp = (
      let (spt,exp2) = compile_pat_bindings t i m exp in
      (insert k one spt,Let t (SOME s) x exp2))`;
   `compile_pat_bindings t i (((Plit _5:pattern_semantics_pat),_6,_7) ::
  m) exp =
      compile_pat_bindings t i m exp`;
   `compile_pat_bindings t i (((Pcon _8 ps:pattern_semantics_pat),k,x)
  :: m) exp = (
      let j_nms = MAP (\(j,p). let k = i + 1 + j in
          let nm = enc_num_to_name k in
          ((j,nm),(p,k,Var_local t nm))) (enumerate 0 ps) in
      let (spt,exp2) = compile_pat_bindings t (i + 2 + LENGTH ps)
          (MAP SND j_nms ++ m) exp in
      let j_nms_used = FILTER (\(_9,(_10,k,_11)). IS_SOME (lookup k
        spt)) j_nms in
      let exp3 = ITLIST (\((j,nm),_12) exp.
          flatLang_Let t (SOME nm) (App t (El j) [x]) exp)
            j_nms_used exp2 in
      let spt2 = if NULL j_nms_used then spt else insert k one spt
        in
      (spt2,exp3))`;
   `compile_pat_bindings t i (((Pas p v:pattern_semantics_pat),k,x) ::
  m) exp = (
      let nm = enc_num_to_name (i + 1) in
      let (spt,exp2) = compile_pat_bindings t (i + 2)
                        ((p,i + 1,Var_local t nm) :: m) exp in
      (insert k one spt,Let t (SOME v) x
                              (Let t (SOME nm) (Var_local t v)
                                exp2)))`;
   `compile_pat_bindings t i (((Pref p:pattern_semantics_pat),k,x) :: m)
  exp = (
      let nm = enc_num_to_name (i + 1) in
      let (spt,exp2) = compile_pat_bindings t (i + 2)
          ((p,i + 1,Var_local t nm) :: m) exp in
      (insert k one spt,Let t (SOME nm) (App t (El 0) [x]) exp2))`];;

let compile_pat_rhs_def = cake_define
  `compile_pat_rhs t i v (p,exp) =
   SND (compile_pat_bindings t (i + 1) [(p,i,v)] exp)`;;

let decode_pos_def = cake_define_list
  [`decode_pos t v EmptyPos = v`;
   `decode_pos t v (Pos i pos:position) = decode_pos t (App t (El i)
  [v]) pos`];;

let decode_test_def = cake_define_list
  [`flat_pattern_decode_test t (TagLenEq tag l:dTest) v = App t
  (TagLenEq tag l) [v]`;
   `flat_pattern_decode_test t (LitEq lit:dTest) v = App t (Src
  Equality) [v; Lit t lit]`];;
hol4_overload "decode_test" "flat_pattern_decode_test";;

let simp_guard_def = cake_define
  `simp_guard x =
      match x with
        Conj x y ->
     (let v = simp_guard x in
      let w = simp_guard y in
      if v = Not True \/ w = Not True then
        Not True else if v = True then w else if w = True then v else
          Conj v w)
      | (Disj x y) ->
     (let v = simp_guard x in
      let w = simp_guard y in
      if v = True \/ w = True then
        True else if v = Not True then w else if w = Not True then v
          else Disj v w)
      | (Not x) ->
     (let v = simp_guard x in
      match v with
        Not True -> True | Not w -> w | _13 -> Not v)
      | x -> x`;;

let decode_guard_def = cake_define_list
  [`decode_guard t v (Not gd:dGuard) = App t (Src Equality)
  [decode_guard t v gd; Bool t F]`;
   `decode_guard t v (Conj gd1 gd2:dGuard) = SmartIf t (decode_guard t v
  gd1)
      (decode_guard t v gd2) (Bool t F)`;
   `decode_guard t v (Disj gd1 gd2:dGuard) = SmartIf t (decode_guard t v
  gd1) (Bool t T)
      (decode_guard t v gd2)`;
   `decode_guard t v True = Bool t T`;
   `decode_guard t v (PosTest pos test:dGuard) = decode_test t test
  (decode_pos t v pos)`];;

let decode_dtree_def = cake_define
  `decode_dtree t br_spt v df pattern_semantics$Fail =
      match pattern_semantics$Fail with
        Leaf n -> (match lookup n br_spt with SOME br -> br | NONE ->
          df)
      | pattern_semantics_Fail -> df
      | TypeFail -> Var_local t (implode "impossible-case")
      | (If guard dt1 dt2) ->
   (let guard = simp_guard guard in
   let dec1 = decode_dtree t br_spt v df dt1 in
   let dec2 = decode_dtree t br_spt v df dt2 in
   if guard = True then dec1 else if guard = Not True then dec2
     else SmartIf t (decode_guard t v guard) dec1 dec2)`;;

let _ = size_thms "pat";;
(* HOL4 termination: \\ rw [pat1_size] \\ fs [MEM_SPLIT, SUM_APPEND] *)
let encode_pat_def = cake_define_wf
  `MEASURE pat_size`
  `encode_pat x1 =
      match x1 with
        flatLang_Pany -> pattern_semantics_Any
      | (Plit l) -> Lit l
      | (Pvar _14) -> Any
      | (flatLang_Pcon stmp ps) -> Cons
     (match stmp with NONE -> NONE | SOME (i,NONE) -> SOME (i,NONE) |
       SOME (i,SOME (ty,ctors)) -> SOME (i,SOME ctors))
     (MAP encode_pat ps)
      | (Pas p v) -> encode_pat p
      | (Pref p) -> Ref (encode_pat p)`;;

let _ = size_thms "pat";;
(* HOL4 termination: \\ simp [flatLangTheory.pat_size_def] \\ rw []
   \\ simp [o_DEF, MAPi_eq_MAP, SUM_APPEND, pat1_size] *)
let naive_pattern_match_def = cake_define_wf
  `MEASURE (\x. SUM (MAP (pat_size o FST) (SND x)) + LENGTH (SND x))`
  `naive_pattern_match t x2 =
      match x2 with
        [] -> Bool t T
      | ((flatLang_Pany,_15) :: mats) -> naive_pattern_match t mats
      | ((Pvar _16,_17) :: mats) -> naive_pattern_match t mats
      | ((Plit l,v) :: mats) -> SmartIf t
     (App t (Src Equality) [v; Lit t l]) (naive_pattern_match t mats)
       (Bool t F)
      | ((Pcon NONE ps,v) :: mats) ->
     naive_pattern_match t (MAPi (\i p. (p,App t (El i) [v])) ps ++
       mats)
      | ((Pas p i,v) :: mats) ->
     naive_pattern_match t ((p,v) :: mats)
      | ((Pcon (SOME stmp) ps,v) :: mats) ->
     SmartIf t (App t (TagLenEq (FST stmp) (LENGTH ps)) [v])
       (naive_pattern_match t (MAPi (\i p. (p,App t (El i) [v])) ps
         ++ mats))
       (Bool t F)
      | ((Pref p,v) :: mats) ->
     naive_pattern_match t ((p,App t (El 0) [v]) :: mats)`;;

let naive_pattern_matches_def = cake_define_list
  [`naive_pattern_matches t v [] dflt_x = dflt_x`;
   `naive_pattern_matches t v ((p,x) :: ps) dflt_x =
    SmartIf t (naive_pattern_match t [(p,v)]) x
      (naive_pattern_matches t v ps dflt_x)`];;

let compile_pats_def = cake_define
  `compile_pats (cfg:flat_pattern_config) naive t i v default_x ps =
   (let branches = MAP (compile_pat_rhs t i v) ps in
   if naive then
   naive_pattern_matches t v (ZIP (MAP FST ps) branches) default_x
     else let pats = MAPi (\j (p,_18). (encode_pat p,j)) ps in
   let dt = pattern_comp_comp pats in decode_dtree t (fromList
     branches) v default_x dt)`;;

let max_dec_name_def = cake_define_list
  [`max_dec_name [] = 0`;
   `max_dec_name (nm :: nms) = MAX (dec_name_to_num nm) (max_dec_name
  nms)`];;

let op_sets_globals_def = cake_define
  `op_sets_globals x1 =
      match x1 with
        GlobalVarInit n -> T
      | _19 -> F`;;

let compile_exp_def = cake_define_list
  [`flat_pattern_compile_exp cfg (Var_local t vid:flatLang_exp) =
        (dec_name_to_num vid,F,Var_local t vid)`;
   `flat_pattern_compile_exp cfg (Raise t x:flatLang_exp) =
        (let (i,sg,y) = flat_pattern_compile_exp cfg x in
        (i,sg,Raise t y))`;
   `flat_pattern_compile_exp cfg (Handle t x ps:flatLang_exp) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgp,ps2) = compile_match cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = Var_local t nm in
        let r = Raise t v in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),Handle t y [(Pvar nm,exp)]))`;
   `flat_pattern_compile_exp cfg (Con t ts xs:flatLang_exp) =
        (let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs)
          in
        (i,sg,Con t ts (REVERSE ys)))`;
   `flat_pattern_compile_exp cfg (Fun t vs x:flatLang_exp) =
        (let (i,sg,y) = flat_pattern_compile_exp cfg x in
        (i,sg,Fun t vs y))`;
   `flat_pattern_compile_exp cfg (App t op xs:flatLang_exp) =
        (let (i,sg,ys) = flat_pattern_compile_exps cfg (REVERSE xs)
          in
        (i,(sg \/ op_sets_globals op),App t op (REVERSE ys)))`;
   `flat_pattern_compile_exp cfg (Mat t x ps:flatLang_exp) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgp,ps2) = compile_match cfg ps in
        let k = MAX i j + 2 in
        let nm = enc_num_to_name k in
        let v = Var_local t nm in
        let r = Raise t (Con t (SOME (bind_tag,NONE)) []) in
        let exp = compile_pats cfg sgp t k v r ps2 in
        (k,(sgx \/ sgp),Let t (SOME nm) y exp))`;
   `flat_pattern_compile_exp cfg (Let t v x1 x2:flatLang_exp) =
        (let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
        let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
        let k = (match v with NONE -> 0 | SOME vid ->
          dec_name_to_num vid) in
        (MAX i (MAX j k),(sg1 \/ sg2),Let t v y1 y2))`;
   `flat_pattern_compile_exp cfg (flatLang_Letrec t fs x:flatLang_exp) =
        (let ys = MAP (\(a,b,c). (a,b,flat_pattern_compile_exp cfg
          c)) fs in
        let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let j = MAX_LIST (MAP (\(_20,_21,(j,_22,_23)). j) ys) in
        let sgfs = EXISTS (\(_24,_25,(_26,sg,_27)). sg) ys in
        let fs2 = MAP (\(a,b,(_28,_29,exp)). (a,b,exp)) ys in
        (MAX i j,(sgfs \/ sgx),flatLang_Letrec t fs2 y))`;
   `flat_pattern_compile_exp cfg (If t x1 x2 x3:flatLang_exp) =
        (let (i,sg1,y1) = flat_pattern_compile_exp cfg x1 in
        let (j,sg2,y2) = flat_pattern_compile_exp cfg x2 in
        let (k,sg3,y3) = flat_pattern_compile_exp cfg x3 in
        (MAX i (MAX j k),(sg1 \/ sg2 \/ sg3),SmartIf t y1 y2 y3))`;
   `flat_pattern_compile_exp cfg exp = (0,F,exp)`;
   `flat_pattern_compile_exps cfg [] = (0,F,[])`;
   `flat_pattern_compile_exps cfg (x :: xs) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let (j,sgy,ys) = flat_pattern_compile_exps cfg xs in
        (MAX i j,(sgx \/ sgy),y :: ys))`;
   `compile_match cfg [] = (0,F,[])`;
   `compile_match cfg ((p,x) :: ps) =
        (let (i,sgx,y) = flat_pattern_compile_exp cfg x in
        let j = max_dec_name (pat_bindings p) in
        let (k,sgp,ps2) = compile_match cfg ps in
        (MAX i (MAX j k),(sgx \/ sgp),((p,y) :: ps2)))`];;
hol4_overload "compile_exp" "flat_pattern_compile_exp";;
hol4_overload "compile_exps" "flat_pattern_compile_exps";;

let compile_dec_def = cake_define
  `compile_dec cfg exp = SND (SND (compile_exp cfg exp))`;;
