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

(**************************** ANALYSIS FUNCTIONS
   *****************************)

(* is_hidden exp = T means there is no direct execution of
   GlobalVarLookup *)
let is_hidden_def = cake_define
  `is_hidden x1 =
        match x1 with
          (flatLang_Raise t e) -> is_hidden e
        | (flatLang_Handle t e pes) -> F
        | (flatLang_Lit t l) -> T
        | (flatLang_Con t id_option es) -> EVERY is_hidden es
        | (flatLang_Var_local t str) -> T
        | (flatLang_Fun t name body) -> T
        | (flatLang_App t (flatLang_Src ast_Opapp) l) -> F
        | (flatLang_App t (flatLang_GlobalVarInit g) [e]) ->
          is_hidden e
        | (flatLang_App t (flatLang_GlobalVarLookup g) [e]) -> F
        | (flatLang_If t e1 e2 e3) -> (is_hidden e1 /\ is_hidden e2
          /\ is_hidden e3)
        | (flatLang_Mat t e1 [p,e2]) -> (is_hidden e1 /\ is_hidden
          e2)
        | (flatLang_Let t opt e1 e2) -> (is_hidden e1 /\ is_hidden
          e2)
        | (flatLang_Letrec t funs e) -> is_hidden e
        | _1 -> F`;;

let total_pat_def = cake_define
  `total_pat x1 =
      match x1 with
        flatLang_Pany -> T
      | (flatLang_Pvar _2) -> T
      | (flatLang_Pcon NONE xs) -> total_pat_list xs
      | (flatLang_Pas p _3) -> total_pat p
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
          (flatLang_Handle t e pes) -> flat_elim_is_pure e
        | (flatLang_Lit t l) -> T
        | (flatLang_Con t id_option es) -> EVERY flat_elim_is_pure es
        | (flatLang_Var_local t str) -> T
        | (flatLang_Fun t name body) -> T
        | (flatLang_App t (flatLang_GlobalVarInit g) es) -> EVERY
          flat_elim_is_pure es
        | (flatLang_If t e1 e2 e3) -> (flat_elim_is_pure e1 /\
          flat_elim_is_pure e2 /\ flat_elim_is_pure e3)
        | (flatLang_Mat t e1 pes) ->
         (flat_elim_is_pure e1 /\ EVERY flat_elim_is_pure (MAP SND
           pes) /\ EXISTS total_pat (MAP FST pes))
        | (flatLang_Let t opt e1 e2) -> (flat_elim_is_pure e1 /\
          flat_elim_is_pure e2)
        | (flatLang_Letrec t funs e) -> flat_elim_is_pure e
        | _5 -> F`;;

let has_Eval_def = cake_define
  `has_Eval x1 =
        match x1 with
          (flatLang_App t flatLang_op es) -> flatLang_op =
            flatLang_Src ast_Eval \/ has_Eval_list es
        | (flatLang_Mat _6 e pes) -> has_Eval e \/ has_Eval_pats pes
        | (flatLang_Letrec _7 funs e) -> has_Eval e \/ has_Eval_funs
          funs
        | (flatLang_Raise _8 e) -> has_Eval e
        | (flatLang_Handle _9 e pes) -> has_Eval e \/ has_Eval_pats
          pes
        | (flatLang_Con _10 _11 es) -> has_Eval_list es
        | (flatLang_Fun _12 _13 e) -> has_Eval e
        | (flatLang_If _14 e1 e2 e3) -> has_Eval e1 \/ has_Eval e2 \/
          has_Eval e3
        | (flatLang_Let _15 _16 e1 e2) -> has_Eval e1 \/ has_Eval e2
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

(* HOL4 termination: >> rw[list_size_pair_size_MAP_FST_SND] *)
let find_loc_def = cake_define_wf
  `MEASURE (\e. match e with INL x -> exp_size x | INR y -> list_size
  exp_size y)`
  `(find_loc ((flatLang_Raise _22 er):flatLang_exp) = find_loc er) /\
   (find_loc (flatLang_Handle _23 eh p_es) =
       sptree_union (find_loc eh) (find_locL (MAP SND p_es))) /\
   (find_loc (flatLang_Lit _24 _25) = (LN:one spt)) /\
   (find_loc (flatLang_Con _26 _27 es) = find_locL es) /\
   (find_loc (flatLang_Var_local _28 _29) = LN) /\
   (find_loc (flatLang_Fun _30 _31 ef) = find_loc ef) /\
   (find_loc (flatLang_App _32 flatLang_op es) = (match
     (dest_GlobalVarInit flatLang_op) with SOME n -> (sptree_insert n
     one (find_locL es)) | NONE -> find_locL es)) /\
   (find_loc (flatLang_If _33 ei1 ei2 ei3) =
       sptree_union (find_loc ei1) (sptree_union (find_loc ei2)
         (find_loc ei3))) /\
   (find_loc (flatLang_Mat _34 em p_es) =
       sptree_union (find_loc em) (find_locL (MAP SND p_es))) /\
   (find_loc (flatLang_Let _35 _36 el1 el2) = sptree_union (find_loc
     el1) (find_loc el2)) /\
   (find_loc (flatLang_Letrec _37 vv_es elr1) =
       sptree_union (find_locL (MAP (SND o SND) vv_es)) (find_loc
         elr1)) /\
   (find_locL [] = LN) /\
   (find_locL (e :: es) = sptree_union (find_loc e) (find_locL
     es))`;;

(* HOL4 termination: >> rw[list_size_pair_size_MAP_FST_SND] *)
let find_lookups_def = cake_define_wf
  `MEASURE (\e. match e with INL x -> exp_size x | INR (y:flatLang_exp
  list) ->
                 list_size exp_size y)`
  `(find_lookups (flatLang_Raise _38 er) = find_lookups er) /\
   (find_lookups (flatLang_Handle _39 eh p_es) =
       sptree_union (find_lookups eh) (find_lookupsL (MAP SND p_es)))
         /\
   (find_lookups (flatLang_Lit _40 _41) = LN) /\
   (find_lookups (flatLang_Con _42 _43 es) = find_lookupsL es) /\
   (find_lookups (flatLang_Var_local _44 _45) = LN) /\
   (find_lookups (flatLang_Fun _46 _47 ef) = find_lookups ef) /\
   (find_lookups (flatLang_App _48 flatLang_op es) = (match
     (dest_GlobalVarLookup flatLang_op) with SOME n -> (sptree_insert n
     one (find_lookupsL es)) | NONE -> find_lookupsL es)) /\
   (find_lookups (flatLang_If _49 ei1 ei2 ei3) =
       sptree_union (find_lookups ei1)
           (sptree_union (find_lookups ei2) (find_lookups ei3))) /\
   (find_lookups (flatLang_Mat _50 em p_es) =
       sptree_union (find_lookups em) (find_lookupsL (MAP SND p_es)))
         /\
   (find_lookups (flatLang_Let _51 _52 el1 el2) =
       sptree_union (find_lookups el1) (find_lookups el2)) /\
   (find_lookups (flatLang_Letrec _53 vv_es elr1) =
       sptree_union (find_lookupsL (MAP (SND o SND) vv_es))
         (find_lookups elr1)) /\
   (find_lookupsL [] = LN) /\
   (find_lookupsL (e :: es) = sptree_union (find_lookups e)
     (find_lookupsL es))`;;

let analyse_exp_def = cake_define
  `analyse_exp e = (let locs = (find_loc e) in let lookups =
  (find_lookups e) in
       if flat_elim_is_pure e then (
           if (is_hidden e) then (LN,sptree_map (K lookups) locs)
             else (locs,sptree_map (K lookups) locs)) else (
           (sptree_union locs lookups,(sptree_map (K LN)
             (sptree_union locs lookups)))))`;;

let code_analysis_union_def = cake_define
  `code_analysis_union (r1,t1) (r2,t2) =
       ((sptree_union r1 r2),(num_set_tree_union t1 t2))`;;

let analyse_code_def = cake_define
  `analyse_code [] = (LN,LN) /\
   analyse_code (e :: cs) =
       code_analysis_union (analyse_exp e) (analyse_code cs)`;;


(**************************** REMOVAL FUNCTIONS
   *****************************)

let keep_def = cake_define
  `keep reachable e =
       (if (\t. t = LN) (inter (find_loc e) reachable) then
         (~(flat_elim_is_pure e)) else T)`;;

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
