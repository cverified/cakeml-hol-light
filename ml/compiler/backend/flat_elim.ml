(* ======================================================== *)
(*  flat_elim: ported from HOL4's
    compiler/backend/flat_elimScript.sml
    A definition theory, with 15 definitions and 3 theorems.  Needed
    by 6 files of the port.  *)
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "flat_elim"
  ["flatLang"; "misc"];;

(**************************** ANALYSIS FUNCTIONS *****************************)

(* is_hidden exp = T means there is no direct execution of GlobalVarLookup *)
let _ = size_thms "flatLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let is_hidden_def,is_hidden_ind = define_wf
  `MEASURE (\x0. flatLang_exp_size x0)`
  [`is_hidden x1 =
        match x1 with
          (flatLang_Raise t e:flatLang_exp) -> is_hidden e
        // raise exception
        | (flatLang_Handle t e pes) -> F
        // exception handler
        | (flatLang_Lit t l) -> T
        // literal
        | (flatLang_Con t id_option es) -> ALL is_hidden es
        // constructor
        | (flatLang_Var_local t str) -> T
        // local var
        | (flatLang_Fun t name body) -> T
        // function abstraction
        | (flatLang_App t (flatLang_Src ast_Opapp) l) -> F
        // function application
        | (flatLang_App t (flatLang_GlobalVarInit g) [e]) ->
          is_hidden e
        // GlobalVarInit
        | (flatLang_App t (flatLang_GlobalVarLookup g) [e]) -> F
        // GlobalVarLookup
        | (flatLang_If t e1 e2 e3) -> (is_hidden e1 /\ is_hidden e2
          /\ is_hidden e3)
        // if expression
        | (flatLang_Mat t e1 [p,e2]) -> (is_hidden e1 /\ is_hidden
          e2)
        // SINGLE pattern match
        | (flatLang_Let t opt e1 e2) -> (is_hidden e1 /\ is_hidden
          e2)
        // let-expression
        | (flatLang_Letrec t funs e) -> is_hidden e
        // local def of mutually recursive funs
        | _1 -> F`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let total_pat_def,total_pat_ind = define_shaped_rec_cheat
  "maplist>measure"
  [`total_pat (flatLang_Pany:flatLang_pat) = T`;
   `total_pat (flatLang_Pvar _3:flatLang_pat) = T`;
   `total_pat (flatLang_Pcon NONE xs:flatLang_pat) = total_pat_list
    xs`;
   `total_pat (flatLang_Pas p _5:flatLang_pat) = total_pat p`;
   `total_pat _6 = F`;
   `total_pat_list [] = T`;
   `total_pat_list (CONS p ps) = (total_pat p /\ total_pat_list ps)`];;

(* check if expression is pure in that it does not make any visible changes
    (other than writing to globals) *)
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flat_elimScript.sml:75-80: the tactic that proves the
   termination *)
let flat_elim_is_pure_def,flat_elim_is_pure_ind = define_wf
  `MEASURE (\e. flatLang_exp_size e)`
  [`flat_elim_is_pure x1 =
        match x1 with
          (flatLang_Handle t e pes:flatLang_exp) ->
            flat_elim_is_pure e
        | (flatLang_Lit t l) -> T
        | (flatLang_Con t id_option es) -> ALL flat_elim_is_pure es
        | (flatLang_Var_local t str) -> T
        | (flatLang_Fun t name body) -> T
        | (flatLang_App t (flatLang_GlobalVarInit g) es) -> ALL
          flat_elim_is_pure es
        | (flatLang_If t e1 e2 e3) -> (flat_elim_is_pure e1 /\
          flat_elim_is_pure e2 /\ flat_elim_is_pure e3)
        | (flatLang_Mat t e1 pes) ->
         (flat_elim_is_pure e1 /\ ALL flat_elim_is_pure (MAP SND
           pes) /\ EX total_pat (MAP FST pes))
        | (flatLang_Let t opt e1 e2) -> (flat_elim_is_pure e1 /\
          flat_elim_is_pure e2)
        | (flatLang_Letrec t funs e) -> flat_elim_is_pure e
        | _7 -> F`];;

(* HOL4 flat_elimScript.sml:82: a theorem that HOL4 states as the
   value of an ML expression: is_pure_def1 *)

let has_Eval_def,has_Eval_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`has_Eval (flatLang_App t op es:flatLang_exp) <=> op =
    flatLang_Src ast_Eval \/ has_Eval_list es`;
   `has_Eval (flatLang_Mat _9 e pes:flatLang_exp) <=> has_Eval e \/
    has_Eval_pats pes`;
   `has_Eval (flatLang_Letrec _11 funs e:flatLang_exp) <=> has_Eval e
    \/ has_Eval_funs funs`;
   `has_Eval (flatLang_Raise _13 e:flatLang_exp) <=> has_Eval e`;
   `has_Eval (flatLang_Handle _15 e pes:flatLang_exp) <=> has_Eval e
    \/ has_Eval_pats pes`;
   `has_Eval (flatLang_Con _18 _19 es:flatLang_exp) <=> has_Eval_list
    es`;
   `has_Eval (flatLang_Fun _22 _23 e:flatLang_exp) <=> has_Eval e`;
   `has_Eval (flatLang_If _25 e1 e2 e3:flatLang_exp) <=> has_Eval e1
    \/ has_Eval e2 \/ has_Eval e3`;
   `has_Eval (flatLang_Let _28 _29 e1 e2:flatLang_exp) <=> has_Eval
    e1 \/ has_Eval e2`;
   `has_Eval _30 <=> F`;
   `has_Eval_list [] <=> F`;
   `has_Eval_list (CONS e es) <=> has_Eval e \/ has_Eval_list es`;
   `has_Eval_pats [] <=> F`;
   `has_Eval_pats (CONS (p,e) pes) <=> has_Eval e \/ has_Eval_pats
    pes`;
   `has_Eval_funs [] <=> F`;
   `has_Eval_funs (CONS (_31,_32,e) fs) <=> has_Eval e \/
    has_Eval_funs fs`];;

let dest_GlobalVarInit_def = new_definition
  `dest_GlobalVarInit x1 =
    match x1 with
      flatLang_GlobalVarInit n -> SOME n
    | _33 -> NONE`;;

let dest_GlobalVarLookup_def = new_definition
  `dest_GlobalVarLookup x1 =
    match x1 with
      flatLang_GlobalVarLookup n -> SOME n
    | _34 -> NONE`;;

let _ = size_thms "flatLang_pat";;
let exp_size_map_snd = prove
 (`!p_es. list_size flatLang_exp_size (MAP SND p_es) <= list_size
  (pair_size flatLang_pat_size flatLang_exp_size) p_es`,
  CHEAT_TAC);;

let _ = size_thms "mlstring";;
let exp_size_map_snd_snd = prove
 (`!vv_es. list_size flatLang_exp_size (MAP (\x. SND (SND x)) vv_es) <=
  list_size (pair_size mlstring_size
           (pair_size mlstring_size flatLang_exp_size)) vv_es`,
  CHEAT_TAC);;

let find_loc_def,find_loc_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`find_loc ((flatLang_Raise _35 er):flatLang_exp) = ((find_loc
    er):1 spt)`;
   `find_loc (flatLang_Handle _37 eh p_es:flatLang_exp) =
            ((sptree_union (find_loc eh) (find_locL (MAP SND
                p_es))):1 spt)`;
   `find_loc (flatLang_Lit _40 _41:flatLang_exp) = (LN:1 spt)`;
   `find_loc (flatLang_Con _44 _45 es:flatLang_exp) = ((find_locL
    es):1 spt)`;
   `find_loc (flatLang_Var_local _46 _47) = ((LN):1 spt)`;
   `find_loc (flatLang_Fun _50 _51 ef:flatLang_exp) = ((find_loc
    ef):1 spt)`;
   `find_loc (flatLang_App _53 op es:flatLang_exp) = (((match
    (dest_GlobalVarInit op) with SOME n -> (sptree_insert n one
    (find_locL es)) | NONE -> find_locL es)):1 spt)`;
   `find_loc (flatLang_If _55 ei1 ei2 ei3:flatLang_exp) =
            ((sptree_union (find_loc ei1) (sptree_union (find_loc
                ei2) (find_loc ei3))):1 spt)`;
   `find_loc (flatLang_Mat _57 em p_es:flatLang_exp) =
            ((sptree_union (find_loc em) (find_locL (MAP SND
                p_es))):1 spt)`;
   `find_loc (flatLang_Let _60 _61 el1 el2:flatLang_exp) =
    ((sptree_union (find_loc el1) (find_loc el2)):1 spt)`;
   `find_loc (flatLang_Letrec _63 vv_es elr1:flatLang_exp) =
            ((sptree_union (find_locL (MAP (SND o SND) vv_es))
                (find_loc elr1)):1 spt)`;
   `find_locL [] = LN`;
   `find_locL (CONS e es) = sptree_union (find_loc e) (find_locL
    es)`];;

let find_lookups_def,find_lookups_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`find_lookups (flatLang_Raise _65 er:flatLang_exp) = find_lookups
    er`;
   `find_lookups (flatLang_Handle _67 eh p_es:flatLang_exp) =
            sptree_union (find_lookups eh) (find_lookupsL (MAP
                SND p_es))`;
   `find_lookups (flatLang_Lit _70 _71:flatLang_exp) = LN`;
   `find_lookups (flatLang_Con _74 _75 es:flatLang_exp) =
    find_lookupsL es`;
   `find_lookups (flatLang_Var_local _76 _77) = LN`;
   `find_lookups (flatLang_Fun _80 _81 ef:flatLang_exp) =
    find_lookups ef`;
   `find_lookups (flatLang_App _83 op es:flatLang_exp) = (match
    (dest_GlobalVarLookup op) with SOME n -> (sptree_insert n one
    (find_lookupsL es)) | NONE -> find_lookupsL es)`;
   `find_lookups (flatLang_If _85 ei1 ei2 ei3:flatLang_exp) =
            sptree_union (find_lookups ei1)
                (sptree_union (find_lookups ei2) (find_lookups
                    ei3))`;
   `find_lookups (flatLang_Mat _87 em p_es:flatLang_exp) =
            sptree_union (find_lookups em) (find_lookupsL (MAP
                SND p_es))`;
   `find_lookups (flatLang_Let _90 _91 el1 el2:flatLang_exp) =
            sptree_union (find_lookups el1) (find_lookups el2)`;
   `find_lookups (flatLang_Letrec _93 vv_es elr1:flatLang_exp) =
            sptree_union (find_lookupsL (MAP (SND o SND) vv_es))
                (find_lookups elr1)`;
   `find_lookupsL [] = LN`;
   `find_lookupsL (CONS e es) = sptree_union (find_lookups e)
    (find_lookupsL es)`];;

let analyse_exp_def = new_definition
  `analyse_exp e = (let locs = (find_loc e) in let lookups =
  (find_lookups e) in
       if flat_elim_is_pure e then (
           if (is_hidden e) then (LN,sptree_map (K lookups) locs)
             else (locs,sptree_map (K lookups) locs)) else (
           (sptree_union locs lookups,(sptree_map (K LN)
             (sptree_union locs lookups)))))`;;

let code_analysis_union_def = new_definition
  `code_analysis_union (r1,t1) (r2,t2) =
       ((sptree_union r1 r2),(num_set_tree_union t1 t2))`;;

let analyse_code_def,analyse_code_ind = define_rec
  [`analyse_code [] = (LN,LN)`;
   `analyse_code (CONS e cs) =
        code_analysis_union (analyse_exp e) (analyse_code cs)`];;


(**************************** REMOVAL FUNCTIONS *****************************)

let keep_def = new_definition
  `keep reachable e =
       // if none of the global variables that e may assign to are in
       // the reachable set, then e is candidate for removal
       // -> if any are in, then keep e
       // -> however if e is not pure (can have side-effects),
       // then it must be kept
       (if (\t. t = LN) (inter (find_loc e) reachable) then
         (~(flat_elim_is_pure e)) else T)`;;

let remove_unreachable_def = new_definition
  `remove_unreachable reachable l = FILTER (keep reachable) l`;;

let has_Eval_dec_def = new_definition
  `has_Eval_dec e = has_Eval e`;;

let remove_flat_prog_def = new_definition
  `remove_flat_prog code =
     (if EX has_Eval_dec code then code else
       let (r,t) = analyse_code code in
       let reachable = closure_spt r t in
       remove_unreachable reachable code)`;;

(* and the interface *)
let _ = unhide_overloads ();;
