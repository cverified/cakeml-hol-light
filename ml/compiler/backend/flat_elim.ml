(* ======================================================== *)
(*  flat_elim: ported from HOL4's
    compiler/backend/flat_elimScript.sml  *)
(* ======================================================== *)

(*
  Implementation for flatLang dead-code elimination.

  Analyses code to give a next-step function as a num_set num_map.
  Closes this next-step function to give a set of reachable globals.
  Removes unreachable globals from the code.
*)

needs "compiler/backend/flatLang.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(**************************** ANALYSIS FUNCTIONS
   *****************************)

(* is_hidden exp = T means there is no direct execution of
   GlobalVarLookup *)
let is_hidden_def = cake_define
  `is_hidden x1 =
        match x1 with
          (Raise t e) -> is_hidden e
        | (Handle t e pes) -> F
        | (Lit t l) -> T
        | (Con t id_option es) -> EVERY is_hidden es
        | (flatLang_Var_local t str) -> T
        | (Fun t name body) -> T
        | (App t (flatLang_Src ast_Opapp) l) -> F
        | (App t (flatLang_GlobalVarInit g) [e]) -> is_hidden e
        | (App t (flatLang_GlobalVarLookup g) [e]) -> F
        | (If t e1 e2 e3) -> (is_hidden e1 /\ is_hidden e2 /\
          is_hidden e3)
        | (Mat t e1 [p,e2]) -> (is_hidden e1 /\ is_hidden e2)
        | (Let t opt e1 e2) -> (is_hidden e1 /\ is_hidden e2)
        | (Letrec t funs e) -> is_hidden e
        | _1 -> F`;;

let total_pat_def = cake_define
  `total_pat x1 =
      match x1 with
        Pany -> T
      | (Pvar _2) -> T
      | (Pcon NONE xs) -> total_pat_list xs
      | (Pas p _3) -> total_pat p
      | _4 -> F
      | [] -> T
      | (p :: ps) -> (total_pat p /\ total_pat_list ps)`;;

(* check if expression is pure in that it does not make any visible
   changes
    (other than writing to globals) *)
(* HOL4 termination: >> rw[exp_size_def] >> fs[] >> fs [MEM_MAP,
   EXISTS_PROD] >> fs [exp1_size, exp3_size, exp6_size, MEM_SPLIT,
   SUM_APPEND, exp_size_def]>>
   simp[list_size_append,list_size_def,basicSizeTheory.pair_size_def] *)
let is_pure_def = cake_define_wf
  `MEASURE (\e. exp_size e)`
  `flat_elim_is_pure x1 =
        match x1 with
          (Handle t e pes) -> flat_elim_is_pure e
        | (Lit t l) -> T
        | (Con t id_option es) -> EVERY flat_elim_is_pure es
        | (flatLang_Var_local t str) -> T
        | (Fun t name body) -> T
        | (App t (flatLang_GlobalVarInit g) es) -> EVERY
          flat_elim_is_pure es
        | (If t e1 e2 e3) -> (flat_elim_is_pure e1 /\
          flat_elim_is_pure e2 /\ flat_elim_is_pure e3)
        | (Mat t e1 pes) ->
         (flat_elim_is_pure e1 /\ EVERY flat_elim_is_pure (MAP SND
           pes) /\ EXISTS total_pat (MAP FST pes))
        | (Let t opt e1 e2) -> (flat_elim_is_pure e1 /\
          flat_elim_is_pure e2)
        | (Letrec t funs e) -> flat_elim_is_pure e
        | _5 -> F`;;
hol4_overload "is_pure" "flat_elim_is_pure";;

let has_Eval_def = cake_define
  `has_Eval x1 =
        match x1 with
          (App t op es) -> op = flatLang_Src ast_Eval \/
            has_Eval_list es
        | (Mat _6 e pes) -> has_Eval e \/ has_Eval_pats pes
        | (Letrec _7 funs e) -> has_Eval e \/ has_Eval_funs funs
        | (Raise _8 e) -> has_Eval e
        | (Handle _9 e pes) -> has_Eval e \/ has_Eval_pats pes
        | (Con _10 _11 es) -> has_Eval_list es
        | (Fun _12 _13 e) -> has_Eval e
        | (If _14 e1 e2 e3) -> has_Eval e1 \/ has_Eval e2 \/ has_Eval
          e3
        | (Let _15 _16 e1 e2) -> has_Eval e1 \/ has_Eval e2
        | _17 -> F
        | [] -> F
        | (e :: es) -> has_Eval e \/ has_Eval_list es
        | [] -> F
        | ((p,e) :: pes) -> has_Eval e \/ has_Eval_pats pes
        | [] -> F
        | ((_18,_19,e) :: fs) -> has_Eval e \/ has_Eval_funs fs`;;

let dest_GlobalVarInit_def = cake_define
  `dest_GlobalVarInit x1 =
    match x1 with
      (flatLang_GlobalVarInit n) -> SOME n
    | _20 -> NONE`;;

let dest_GlobalVarLookup_def = cake_define
  `dest_GlobalVarLookup x1 =
    match x1 with
      (flatLang_GlobalVarLookup n) -> SOME n
    | _21 -> NONE`;;

let find_loc_def = cake_define_list
  [`find_loc ((Raise _22 er):flatLang_exp) = find_loc er`;
   `find_loc (Handle _23 eh p_es) =
            union (find_loc eh) (find_locL (MAP SND p_es))`;
   `find_loc (Lit _24 _25) = (LN:one spt)`;
   `find_loc (Con _26 _27 es) = find_locL es`;
   `find_loc (flatLang_Var_local _28 _29) = LN`;
   `find_loc (Fun _30 _31 ef) = find_loc ef`;
   `find_loc (App _32 op es) = (match (dest_GlobalVarInit op) with
  SOME n -> (insert n one (find_locL es)) | NONE -> find_locL es)`;
   `find_loc (If _33 ei1 ei2 ei3) =
            union (find_loc ei1) (union (find_loc ei2) (find_loc
              ei3))`;
   `find_loc (Mat _34 em p_es) =
            union (find_loc em) (find_locL (MAP SND p_es))`;
   `find_loc (Let _35 _36 el1 el2) = union (find_loc el1) (find_loc
  el2)`;
   `find_loc (Letrec _37 vv_es elr1) =
            union (find_locL (MAP (SND o SND) vv_es)) (find_loc
              elr1)`;
   `find_locL [] = LN`;
   `find_locL (e :: es) = union (find_loc e) (find_locL es)`];;

let find_lookups_def = cake_define_list
  [`find_lookups (Raise _38 er) = find_lookups er`;
   `find_lookups (Handle _39 eh p_es) =
            union (find_lookups eh) (find_lookupsL (MAP SND p_es))`;
   `find_lookups (Lit _40 _41) = LN`;
   `find_lookups (Con _42 _43 es) = find_lookupsL es`;
   `find_lookups (flatLang_Var_local _44 _45) = LN`;
   `find_lookups (Fun _46 _47 ef) = find_lookups ef`;
   `find_lookups (App _48 op es) = (match (dest_GlobalVarLookup op)
  with SOME n -> (insert n one (find_lookupsL es)) | NONE ->
  find_lookupsL es)`;
   `find_lookups (If _49 ei1 ei2 ei3) =
            union (find_lookups ei1)
                (union (find_lookups ei2) (find_lookups ei3))`;
   `find_lookups (Mat _50 em p_es) =
            union (find_lookups em) (find_lookupsL (MAP SND p_es))`;
   `find_lookups (Let _51 _52 el1 el2) =
            union (find_lookups el1) (find_lookups el2)`;
   `find_lookups (Letrec _53 vv_es elr1) =
            union (find_lookupsL (MAP (SND o SND) vv_es))
              (find_lookups elr1)`;
   `find_lookupsL [] = LN`;
   `find_lookupsL (e :: es) = union (find_lookups e) (find_lookupsL
  es)`];;

let analyse_exp_def = cake_define
  `analyse_exp e = (let locs = (find_loc e) in let lookups =
  (find_lookups e) in
       if is_pure e then (
           if (is_hidden e) then (LN,map (K lookups) locs) else
             (locs,map (K lookups) locs)) else (
           (union locs lookups,(map (K LN) (union locs
             lookups)))))`;;

let code_analysis_union_def = cake_define
  `code_analysis_union (r1,t1) (r2,t2) =
       ((union r1 r2),(num_set_tree_union t1 t2))`;;

let analyse_code_def = cake_define
  `analyse_code [] = (LN,LN) /\
   analyse_code (e :: cs) =
       code_analysis_union (analyse_exp e) (analyse_code cs)`;;


(**************************** REMOVAL FUNCTIONS
   *****************************)

let keep_def = cake_define
  `keep reachable e =
       (if (\t. t = LN) (inter (find_loc e) reachable) then
         (~(is_pure e)) else T)`;;

let remove_unreachable_def = cake_define
  `remove_unreachable reachable l = FILTER (keep reachable) l`;;

let has_Eval_dec_def = cake_define
  `has_Eval_dec e = has_Eval e`;;

let remove_flat_prog_def = cake_define
  `remove_flat_prog code =
     (if EXISTS has_Eval_dec code then code else
       let (r,t) = analyse_code code in
       let reachable = closure_spt r t in
       remove_unreachable reachable code)`;;
