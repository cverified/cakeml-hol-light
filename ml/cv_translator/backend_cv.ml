(* ======================================================== *)
(*  backend_cv: ported from HOL4's
    cv_translator/backend_cvScript.sml
    A definition theory, with 41 definitions and 68 theorems.
    Needed by backend_32_cv.ml, backend_64_cv.ml,
    backend_ag32_cv.ml, backend_arm8_cv.ml and backend_x64_cv.ml.  *)
(* ======================================================== *)

(*
  Translate non-target-specific backend functions to cv equations.
*)

needs "basis/pure/basis_cv.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/serialiser/num_tree_enc_dec.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/inference/infer_cv.ml";;
needs "compiler/inference/unify_cv.ml";;
needs "cv_translator/to_data_cv.ml";;
needs "lib/cv_std.ml";;
needs "lib/mergesort.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_cv"
  ["backend"; "basis_cv"; "export"; "infer_cv"; "mllist"; "to_data_cv";
   "unify_cv"];;

let _ = do_list hide_constant ["id"];;

(* HOL4 backend_cvScript.sml:11: ML code, not ported *)

(* the clauses in three quotations: a is ast_t and locs; es is (_#_)list,
   (_)list, (exp list) and (_#_#_)list; funs is ((varN # varN # exp) list)
   and (_)list; pes is ((pat # exp) list) and (_)list; x is varN and (varN
   option), which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with sum_INL (p,e) -> flat_exp_size e
                        | sum_INR (sum_INL (p,e)) -> list_size flat_exp_size e
                        | sum_INR (sum_INR (sum_INL (p,e))) -> list_size
                          (flat_exp_size o SND) e
                        | sum_INR (sum_INR (sum_INR (p,e))) -> list_size
                          (flat_exp_size o SND o SND) e)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 backend_cvScript.sml:48-56: the tactic that proves the termination *)
let collect_conses_def,collect_conses_ind = define_guess_clauses
  [`(collect_conses p (ast_Raise e) = collect_conses p e) /\
    (collect_conses p (ast_Handle e pes) =
         collect_conses_list2 (collect_conses p e) pes) /\
    (collect_conses p (ast_Mat e pes) =
         collect_conses_list2 (collect_conses p e) pes) /\
    (collect_conses p (ast_Lit l) = p) /\
    (collect_conses p (ast_Var v) = p) /\
    (collect_conses p (ast_Fun x e) = collect_conses p e) /\
    (collect_conses p (ast_Log lop e1 e2) =
         collect_conses (collect_conses p e2) e1) /\
    (collect_conses p (ast_If e1 e2 e3) =
         collect_conses (collect_conses (collect_conses p e3) e2) e1) /\
    (collect_conses p (ast_Tannot e a) = collect_conses p e) /\
    (collect_conses_list p [] = p) /\
    (collect_conses_list2 p [] = p) /\
    (collect_conses_list2 p (CONS (v,e) es) =
         collect_conses_list2 (collect_conses p e) es) /\
    (collect_conses_list3 p [] = p)`;
   `(collect_conses p (ast_Con cn es) =
         match cn with NONE -> collect_conses_list p es
         | SOME c ->
             let x = (c,LENGTH es) in
               collect_conses_list (if MEM x p then p else CONS x p) es) /\
    (collect_conses p (ast_App op es) = collect_conses_list p es) /\
    (collect_conses p (ast_Let x e1 e2) =
         collect_conses (collect_conses p e2) e1) /\
    (collect_conses p (ast_Lannot e a) = collect_conses p e) /\
    (collect_conses_list p (CONS e es) =
         collect_conses_list (collect_conses p e) es)`;
   `(collect_conses p (ast_Letrec funs e) =
         collect_conses_list3 (collect_conses p e) funs) /\
    (collect_conses_list3 p (CONS (v,x,e) es) =
         collect_conses_list3 (collect_conses p e) es)`];;

(* HOL4 backend_cvScript.sml:58: ML code, not ported *)

(* [cv_pre] *)
let collect_conses_pre = prove
 (`(!p v. collect_conses_pre p v) /\
   (!p v. collect_conses_list_pre p v) /\
   (!p v. collect_conses_list2_pre p v) /\
   (!p v. collect_conses_list3_pre p v)`,
  CHEAT_TAC);;

let do_con_checks_def = define_cases
  `(do_con_checks cenv [] = T) /\
   (do_con_checks cenv (CONS (c,n) rest) =
      match nsLookup cenv c with NONE -> F
      | SOME (l,_) -> l = n /\ do_con_checks cenv rest)`;;

(* HOL4 backend_cvScript.sml:78: ML code, not ported *)
(* [cv_pre] *)
let do_con_checks_pre = prove
 (`!cenv v. do_con_checks_pre cenv v`,
  CHEAT_TAC);;

(* [local] *)
let collect_conses_acc_lemma = prove
 (`(!(p:((mlstring,mlstring)namespace_id#num) list) v q p.
      collect_conses p v = q ==>
      set_of_list p UNION set_of_list (collect_conses [] v) = set_of_list q)
        /\
   (!(p:((mlstring,mlstring)namespace_id#num) list) v q p.
      collect_conses_list p v = q ==>
      set_of_list p UNION set_of_list (collect_conses_list [] v) =
        set_of_list q) /\
   (!(p:((mlstring,mlstring)namespace_id#num) list) v q p.
      collect_conses_list2 p v = q ==>
      set_of_list p UNION set_of_list (collect_conses_list2 [] v) =
        set_of_list q) /\
   (!(p:((mlstring,mlstring)namespace_id#num) list) v q p.
      collect_conses_list3 p v = q ==>
      set_of_list p UNION set_of_list (collect_conses_list3 [] v) =
        set_of_list q)`,
  CHEAT_TAC);;

(* [local] *)
let collect_conses_acc = GSYM (SIMP_RULE [] collect_conses_acc_lemma);;

let do_con_checks_set = prove
 (`!xs. do_con_checks cenv xs =
        (!c n. MEM (c,n) xs ==> (?y. nsLookup cenv c = SOME (n,y)))`,
  CHEAT_TAC);;

let do_con_checks_collect_conses_thm = prove
 (`(!(p:((mlstring,mlstring)namespace_id#num) list) v.
      do_con_checks env_c (collect_conses [] v) =
      ast_every_exp (one_con_check env_c) v) /\
   (!(p:((mlstring,mlstring)namespace_id#num) list) v.
      do_con_checks env_c (collect_conses_list [] v) =
      ALL (ast_every_exp (one_con_check env_c)) v) /\
   (!(p:((mlstring,mlstring)namespace_id#num) list) v.
      do_con_checks env_c (collect_conses_list2 [] v) =
      ALL (\(x,e). ast_every_exp (one_con_check env_c) e) v) /\
   (!(p:((mlstring,mlstring)namespace_id#num) list) v.
      do_con_checks env_c (collect_conses_list3 [] v) =
      ALL (\(x,y,e). ast_every_exp (one_con_check env_c) e) v)`,
  CHEAT_TAC);;

let to_do_con_checks_list3 = prove
 (`ALL (\(f,n,e). ast_every_exp (one_con_check env_c) e) funs =
   do_con_checks env_c (collect_conses_list3 [] funs)`,
  CHEAT_TAC);;

let to_do_con_checks = prove
 (`ast_every_exp (one_con_check env_c) e =
   do_con_checks env_c (collect_conses [] e)`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:177: ML code, not ported *)

(* HOL4 backend_cvScript.sml:179-181: ML code, not ported *)

(* [cv_pre] *)
let evaluate_dec_check_cons_dec_list_pre = prove
 (`(!env_c v. evaluate_dec_check_cons_dec_list_pre env_c v) /\
   (!env_c v. evaluate_dec_check_cons_dec_pre env_c v)`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:191-192: ML code, not ported *)

(* HOL4 backend_cvScript.sml:194-206: ML code, not ported *)

(* HOL4 backend_cvScript.sml:208: ML code, not ported *)

(* [local] *)
let make_cv_term_provable = prove
 (`(if n < 30 then x else y) = (if n = 0 then x else if 30 <= n then y else
  x)`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:216-217: ML code, not ported *)

(* [cv_pre,local] *)
let num_list_enc_dec_num_to_chars_pre = prove
 (`!n. num_list_enc_dec_num_to_chars_pre n`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:226: ML code, not ported *)

(* [local,cv_inline] *)
let backend_cv_spt_enc_def = spt_enc_def;;

(* HOL4 backend_cvScript.sml:230-235: ML code, not ported *)

(* environment encoding *)

(* HOL4 backend_cvScript.sml:239-242: ML code, not ported *)

(* HOL4 backend_cvScript.sml:244-267: the ML values that the definitions
   below antiquote *)

(* HOL4 backend_cvScript.sml:269-270: ML code, not ported *)

(* HOL4 backend_cvScript.sml:272: ML code, not ported *)

(* HOL4 backend_cvScript.sml:274-276: ML code, not ported *)

(* HOL4 backend_cvScript.sml:278: ML code, not ported *)

(* closLang const encoding *)

(* HOL4 backend_cvScript.sml:282-284: ML code, not ported *)

(* HOL4 backend_cvScript.sml:286-290: the ML values that the definitions
   below antiquote *)

(* PORT FAILED: Definition const_enc_aux_def: expected ')' but found '@' at
   36 *)
(* HOL4 backend_cvScript.sml:292-295: the definition *)

(* HOL4 backend_cvScript.sml:297: ML code, not ported *)

(* [cv_inline,local] *)
let const_enc_aux_thm = prove
 (`closLang_const_enc' = const_enc_aux /\
   MAP closLang_const_enc' = const_enc_aux_list`,
  CHEAT_TAC);;

(* bvl_exp encoding *)

(* HOL4 backend_cvScript.sml:310-312: ML code, not ported *)

(* HOL4 backend_cvScript.sml:314-318: the ML values that the definitions
   below antiquote *)

(* PORT FAILED: Definition bvl_exp_enc_aux_def: expected ')' but found '@'
   at 34 *)
(* HOL4 backend_cvScript.sml:320-323: the definition *)

(* HOL4 backend_cvScript.sml:325: ML code, not ported *)

(* [cv_inline,local] *)
let bvl_exp_enc_aux_thm = prove
 (`bvl_exp_enc' = bvl_exp_enc_aux /\
   MAP bvl_exp_enc' = bvl_exp_enc_aux_list`,
  CHEAT_TAC);;

(* bvi_exp encoding *)

(* the handler recurses under an option, so [option_enc'] is unfolded
   here too, unlike the blocks above. *)
(* HOL4 backend_cvScript.sml:340-343: ML code, not ported *)

(* HOL4 backend_cvScript.sml:345-349: the ML values that the definitions
   below antiquote *)

(* PORT FAILED: Definition bvi_exp_enc_aux_def: expected ')' but found '@'
   at 34 *)
(* HOL4 backend_cvScript.sml:351-354: the definition *)

(* HOL4 backend_cvScript.sml:356: ML code, not ported *)

(* [cv_inline,local] *)
let bvi_exp_enc_aux_thm = prove
 (`bvi_exp_enc' = bvi_exp_enc_aux /\
   MAP bvi_exp_enc' = bvi_exp_enc_aux_list`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:369: ML code, not ported *)

(* closLang_exp encoding *)

(* HOL4 backend_cvScript.sml:373-376: ML code, not ported *)

(* HOL4 backend_cvScript.sml:378-384: the ML values that the definitions
   below antiquote *)

(* PORT FAILED: Definition closLang_exp_enc_aux_def: expected ')' but found
   '@' at 28 *)
(* HOL4 backend_cvScript.sml:386-391: the definition *)

(* HOL4 backend_cvScript.sml:393: ML code, not ported *)

(* [cv_pre,local] *)
let closLang_exp_enc_aux_pre = prove
 (`(!v. closLang_exp_enc_aux_pre v) /\
   (!v. closLang_exp_enc_aux_list_pre v) /\
   (!v. closLang_exp_enc_aux_list1_pre v)`,
  CHEAT_TAC);;

(* [cv_inline,local] *)
let closLang_exp_enc_aux_thm = prove
 (`closLang_exp_enc' = closLang_exp_enc_aux /\
   MAP closLang_exp_enc' = closLang_exp_enc_aux_list /\
   MAP (pair_enc' num_enc' closLang_exp_enc') = closLang_exp_enc_aux_list1`,
  CHEAT_TAC);;

(* closLang val_approx encoding *)

(* HOL4 backend_cvScript.sml:417-419: ML code, not ported *)

(* HOL4 backend_cvScript.sml:421-425: the ML values that the definitions
   below antiquote *)

(* PORT FAILED: Definition val_approx_enc_aux_def: expected ')' but found
   '@' at 41 *)
(* HOL4 backend_cvScript.sml:427-430: the definition *)

(* HOL4 backend_cvScript.sml:432: ML code, not ported *)

(* [cv_inline,local] *)
let val_approx_enc_aux_thm = prove
 (`clos_known_val_approx_enc' = val_approx_enc_aux /\
   MAP clos_known_val_approx_enc' = val_approx_enc_aux_list`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:443: ML code, not ported *)

(* HOL4 backend_cvScript.sml:445-447: ML code, not ported *)

(* ------------------------------------------------------------------------ *)

(* HOL4 backend_cvScript.sml:451-462: ML code, not ported *)

let split_at_pki_def,split_at_pki_ind = define_guess
  `(split_at_pki p k [] i acc = k (REVERSE acc) []) /\
   (split_at_pki p k (CONS h t) i acc =
      if p i h then k (REVERSE acc) (CONS h t) else split_at_pki p k t
          (i + (1:num)) (CONS h acc))`;;

(* [cv_inline] *)
let split_at_pki_thm = prove
 (`splitAtPki p k xs = split_at_pki p k (xs:'a list) 0 []`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:483-485: ML code, not ported *)

let map_pair_def,map_pair_ind = define_guess
  `(map_pair f g [] = []) /\
   (map_pair f g (CONS (x,y) xs) = CONS (f x,g y) (map_pair f g xs))`;;

(* [cv_inline] *)
let map_pair_thm = prove
 (`MAP (f ## g) = map_pair f g`,
  CHEAT_TAC);;

let max_var_exp_list_def = new_definition
  `max_var_exp_list ls = MAX_LIST (MAP (\x. max_var_exp x) ls)`;;

(* [local] *)
let max_var_exp_list_thm = prove
 (`max_var_exp_list ([]:('a word_exp) list) = 0 /\
   (!e (es:('a word_exp) list).
     max_var_exp_list (CONS e es) = MAX (max_var_exp e) (max_var_exp_list
       es))`,
  CHEAT_TAC);;

let max_var_exp_eq =
  REWRITE_RULE [GSYM max_var_exp_list_def] (end_itlist CONJ (CONJUNCTS (CONJ
  max_var_exp_def max_var_exp_list_thm)));;

(* HOL4 backend_cvScript.sml:515-517: ML code, not ported *)

let check_partial_col'_def = new_definition
  `check_partial_col' f xs t ft = check_partial_col (total_colour f) xs t ft`;;

let check_col'_def = new_definition
  `check_col' f t = check_col (total_colour f) t`;;

let check_clash_tree'_def = new_definition
  `check_clash_tree' f x live flive = check_clash_tree (total_colour f) x
  live flive`;;

let apply_nummap_key'_def = new_definition
  `apply_nummap_key' f = apply_nummap_key (total_colour f)`;;

let apply_nummaps_key'_def = new_definition
  `apply_nummaps_key' f = apply_nummaps_key (total_colour f)`;;

let apply_colour_imm'_def = new_definition
  `apply_colour_imm' f = apply_colour_imm (total_colour f)`;;

let apply_colour_exp'_def = new_definition
  `apply_colour_exp' f = apply_colour_exp (total_colour f)`;;

let apply_colour_exp'_list_def = new_definition
  `apply_colour_exp'_list f = MAP (\x. apply_colour_exp' f x)`;;

let apply_colour_inst'_def = new_definition
  `apply_colour_inst' f = apply_colour_inst (total_colour f)`;;

let apply_colour'_def = new_definition
  `apply_colour' f = apply_colour (total_colour f)`;;

(* HOL4 backend_cvScript.sml:559-569: ML code, not ported *)

(* HOL4 backend_cvScript.sml:571-575: the ML values that the definitions
   below antiquote *)

(* HOL4 backend_cvScript.sml:577: a theorem that HOL4 states as the value of
   an ML expression: check_partial_col'_eq *)
(* HOL4 backend_cvScript.sml:578: a theorem that HOL4 states as the value of
   an ML expression: check_col'_eq *)
(* HOL4 backend_cvScript.sml:579: a theorem that HOL4 states as the value of
   an ML expression: check_clash_tree'_eq *)
(* HOL4 backend_cvScript.sml:580: a theorem that HOL4 states as the value of
   an ML expression: apply_colour'_eq *)
(* HOL4 backend_cvScript.sml:581: a theorem that HOL4 states as the value of
   an ML expression: apply_colour_inst'_eq *)
(* HOL4 backend_cvScript.sml:582: a theorem that HOL4 states as the value of
   an ML expression: apply_colour_imm'_eq *)
(* HOL4 backend_cvScript.sml:583: a theorem that HOL4 states as the value of
   an ML expression: apply_colour_nummap_key'_eq *)
(* HOL4 backend_cvScript.sml:584: a theorem that HOL4 states as the value of
   an ML expression: apply_colour_nummaps_key'_eq *)
(* HOL4 backend_cvScript.sml:585-588: a theorem that HOL4 states as the
   value of an ML expression: apply_colour_exp'_eq *)

(* HOL4 backend_cvScript.sml:590-591: the ML values that the definitions
   below antiquote *)

let every_stack_var'_def = new_definition
  `every_stack_var' m = every_stack_var (\n. m <= (n:num))`;;

let every_name'_def = new_definition
  `every_name' m = every_name (\n. m <= (n:num))`;;

(* HOL4 backend_cvScript.sml:601: ML code, not ported *)

(* HOL4 backend_cvScript.sml:603-605: ML code, not ported *)

(* HOL4 backend_cvScript.sml:607: a theorem that HOL4 states as the value of
   an ML expression: every_stack_var'_eq *)
(* HOL4 backend_cvScript.sml:608: a theorem that HOL4 states as the value of
   an ML expression: every_name'_eq *)

(* HOL4 backend_cvScript.sml:610-612: a theorem that HOL4 states as the
   value of an ML expression: oracle_colour_ok_eq *)

(* HOL4 backend_cvScript.sml:614: ML code, not ported *)

(* HOL4 backend_cvScript.sml:616: ML code, not ported *)

(* HOL4 backend_cvScript.sml:618: ML code, not ported *)
(* [cv_pre] *)
let check_partial_col'_pre = prove
 (`!colour v t ft. check_partial_col'_pre colour v t ft`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:625: ML code, not ported *)
(* [cv_pre] *)
let check_clash_tree'_pre = prove
 (`!colour v live flive. check_clash_tree'_pre colour v live flive`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:632-633: ML code, not ported *)

let get_reads_exp_list_def = new_definition
  `get_reads_exp_list xs = FLAT (MAP (\a. get_reads_exp a) xs)`;;

(* [local] *)
let get_reads_exp_list_thm = prove
 (`get_reads_exp_list ([]:('a word_exp) list) = [] /\
   (!x (xs:('a word_exp) list).
     get_reads_exp_list (CONS x xs) = APPEND (get_reads_exp x)
       (get_reads_exp_list xs))`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:647-649: a theorem that HOL4 states as the
   value of an ML expression: get_reads_exp_eq *)


let get_live_exps_def = new_definition
  `get_live_exps ls = big_union (MAP (\a. get_live_exp a) ls)`;;

(* [local] *)
let get_live_exps_thm = prove
 (`get_live_exps ([]:('a word_exp) list) = LN /\
   get_live_exps (CONS x (xs:('a word_exp) list)) = sptree_union
     (get_live_exp x) (get_live_exps xs)`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:663-666: a theorem that HOL4 states as the
   value of an ML expression: get_live_exp_eq *)

(* HOL4 backend_cvScript.sml:668: ML code, not ported *)

(* [cv_pre] *)
let word_alloc_get_live_exp_pre = prove
 (`(!(v:'a word_exp). word_alloc_get_live_exp_pre v) /\
   (!(v:('a word_exp) list). get_live_exps_pre v)`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:677-678: ML code, not ported *)

let pull_exp_list_def = new_definition
  `pull_exp_list ls = MAP (\a. pull_exp a) ls`;;

(* [local] *)
let pull_exp_list_thm = prove
 (`pull_exp_list ([]:('a word_exp) list) = [] /\
   (!x (xs:('a word_exp) list).
     pull_exp_list (CONS x xs) = CONS (pull_exp x) (pull_exp_list xs))`,
  CHEAT_TAC);;

let pull_exp_eq =
  REWRITE_RULE [GSYM pull_exp_list_def] (end_itlist CONJ (CONJUNCTS (CONJ
  pull_exp_def pull_exp_list_thm)));;

let flatten_exp_list_def = new_definition
  `flatten_exp_list ls = MAP (\a. flatten_exp a) ls`;;

(* [local] *)
let flatten_exp_list_thm = prove
 (`flatten_exp_list ([]:('a word_exp) list) = [] /\
   (!x (xs:('a word_exp) list).
     flatten_exp_list (CONS x xs) = CONS (flatten_exp x) (flatten_exp_list
       xs))`,
  CHEAT_TAC);;

let flatten_exp_eq =
  REWRITE_RULE [GSYM flatten_exp_list_def] (end_itlist CONJ (CONJUNCTS (CONJ
  flatten_exp_def flatten_exp_list_thm)));;

(* HOL4 backend_cvScript.sml:712: ML code, not ported *)

let lookup_listCmp_def = new_definition
  `lookup_listCmp = balanced_map_lookup listCmp`;;

(* HOL4 backend_cvScript.sml:718: ML code, not ported *)

(* HOL4 backend_cvScript.sml:720-722: the ML values that the definitions
   below antiquote *)

(* HOL4 backend_cvScript.sml:724: ML code, not ported *)
(* [cv_pre] *)
let lookup_listCmp_pre = prove
 (`!k v. lookup_listCmp_pre k v`,
  CHEAT_TAC);;

let insert_listCmp_def = new_definition
  `insert_listCmp = sptree_insert listCmp`;;

(* HOL4 backend_cvScript.sml:735-737: the ML values that the definitions
   below antiquote *)

(* HOL4 backend_cvScript.sml:739-741: ML code, not ported *)

(* HOL4 backend_cvScript.sml:743-745: ML code, not ported *)

(* HOL4 backend_cvScript.sml:747: ML code, not ported *)
(* [cv_pre] *)
let insert_listCmp_pre = prove
 (`!k v t. insert_listCmp_pre k v t`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:754-794: ML code, not ported *)

(* HOL4 backend_cvScript.sml:796: ML code, not ported *)
(* [cv_pre,local] *)
let word_cse_word_cse_pre = prove
 (`!data v. word_cse_word_cse_pre data v`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:804: ML code, not ported *)

(* HOL4 backend_cvScript.sml:806-809: ML code, not ported *)

let ssa_cc_trans_exp_list_def = new_definition
  `ssa_cc_trans_exp_list t = MAP (\a. ssa_cc_trans_exp t a)`;;

(* [local] *)
let list_thm = prove
 (`(!t. ssa_cc_trans_exp_list t ([]:('a word_exp) list) = []) /\
   (!x (xs:('a word_exp) list) t.
     ssa_cc_trans_exp_list t (CONS x xs) = CONS (ssa_cc_trans_exp t x)
       (ssa_cc_trans_exp_list t xs))`,
  CHEAT_TAC);;

let ssa_cc_trans_exp_eq =
  SIMP_RULE [GSYM ssa_cc_trans_exp_list_def] (end_itlist CONJ (CONJUNCTS
  (CONJ ssa_cc_trans_exp_def list_thm)));;

let const_fp_exp_list_def = new_definition
  `const_fp_exp_list ls cs = MAP (\a. const_fp_exp a cs) ls`;;

(* list_thm[local] *)
let backend_cv_list_thm = prove
 (`(!cs. const_fp_exp_list ([]:('a word_exp) list) cs = []) /\
   (!x (xs:('a word_exp) list) cs.
     const_fp_exp_list (CONS x xs) cs = CONS (const_fp_exp x cs)
       (const_fp_exp_list xs cs))`,
  CHEAT_TAC);;

let const_fp_exp_eq =
  SIMP_RULE [GSYM const_fp_exp_list_def] (end_itlist CONJ (CONJUNCTS (CONJ
  const_fp_exp_def backend_cv_list_thm)));;

(* HOL4 backend_cvScript.sml:843-847: ML code, not ported *)

(* HOL4 backend_cvScript.sml:849: ML code, not ported *)

(* [cv_pre] *)
let word_simp_push_out_if_aux_pre = prove
 (`!p. word_simp_push_out_if_aux_pre p`,
  CHEAT_TAC);;
(* HOL4 backend_cvScript.sml:857: ML code, not ported *)

(* HOL4 backend_cvScript.sml:859: ML code, not ported *)

let adjust_vars_def,adjust_vars_ind = define_guess
  `(adjust_vars [] = []) /\
   (adjust_vars (CONS x xs) = CONS (adjust_var x) (adjust_vars xs))`;;

let to_adjust_vars = prove
 (`MAP adjust_var = adjust_vars`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:872-881: ML code, not ported *)

let get_words_def,get_words_ind = define_guess
  `get_words x1 =
   match x1 with
     [] -> []
   | CONS (_,word_Word w) ws -> CONS w (get_words ws)
   | CONS _ ws -> CONS (n2w 0) (get_words ws)`;;

let to_get_words = prove
 (`MAP (get_Word o SND) ws = get_words ws`,
  CHEAT_TAC);;

let map_compile_part_def,map_compile_part_ind = define_guess
  `(map_compile_part c [] = []) /\
   (map_compile_part c (CONS p ps) = CONS (data_to_word_compile_part c p)
    (map_compile_part c ps))`;;

let to_map_compile_part = prove
 (`!ps. MAP (bvi_to_data_compile_part c) ps = map_compile_part c ps`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:907-911: ML code, not ported *)

(* HOL4 backend_cvScript.sml:913-914: ML code, not ported *)

let sort_canonize_def = new_definition
  `sort_canonize ls =
     sort (total_colour colour) ls`;;

let merge_tail_canonize_def = new_definition
  `merge_tail_canonize b ls accl accr =
     merge_tail b (total_colour colour) ls accl accr`;;

(* HOL4 backend_cvScript.sml:926-929: ML code, not ported *)

(* HOL4 backend_cvScript.sml:931: ML code, not ported *)

(* [cv_pre] *)
let merge_tail_canonize_pre = prove
 (`!negate' v0 v acc. merge_tail_canonize_pre negate' v0 v acc`,
  CHEAT_TAC);;

let mergesortN_tail_canonize_def = new_definition
  `mergesortN_tail_canonize b n ls =
     mergesortN_tail b (total_colour colour) n ls`;;

(* HOL4 backend_cvScript.sml:951-954: ML code, not ported *)

(* [local] *)
let c2b_b2c = prove
 (`c2b (b2c b) = b`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:963: ML code, not ported *)

(* HOL4 backend_cvScript.sml:965-973: a proof *)

(* [cv_pre] *)
let mergesortN_tail_canonize_pre = prove
 (`!negate' n l. mergesortN_tail_canonize_pre negate' n l`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:984: ML code, not ported *)

(* HOL4 backend_cvScript.sml:986: ML code, not ported *)

(* HOL4 backend_cvScript.sml:988: ML code, not ported *)

(* HOL4 backend_cvScript.sml:990-995: ML code, not ported *)

(* [local] *)
let eq_toChar = prove
 (`!n. n < 16 ==> EL n "0123456789ABCDEF" = toChar n`,
  CHEAT_TAC);;

let byte_to_string_eq_toChar_toChar = prove
 (`byte_to_string b =
     implode (CONS (CHR 48) (CONS (CHR 120) (CONS (toChar (w2n b DIV 16))
                              (CONS (toChar (w2n b MOD 16)) []))))`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:1016: ML code, not ported *)
(* [cv_pre] *)
let export_byte_to_string_pre = prove
 (`!b. export_byte_to_string_pre b`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:1027: ML code, not ported *)

let chunks16_def,chunks16_ind = define_guess
  `chunks16 f xs =
     match xs with
       [] -> misc_Nil
     | (CONS x0 (CONS x1 (CONS x2 (CONS x3 (CONS x4 (CONS x5 (CONS x6 (CONS
       x7 (CONS x8 (CONS x9 (CONS x10 (CONS x11 (CONS x12 (CONS x13 (CONS x14
       (CONS x15 ys)))))))))))))))) ->
          SmartAppend
            (f [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13;
              x14; x15])
            (chunks16 f ys)
     | other -> f other`;;

let split16_eq_chunks16 = prove
 (`!f xs. split16 f xs = chunks16 f xs`,
  CHEAT_TAC);;

let comma_cat_byte_to_string_def,comma_cat_byte_to_string_ind = define_guess
  `comma_cat_byte_to_string x =
    match x with
      [] -> [newl_strlit]
    | [x] -> [byte_to_string x; newl_strlit]
    | (CONS x xs) -> CONS (byte_to_string x) (CONS comm_strlit
      (comma_cat_byte_to_string xs))`;;

let comma_cat_word_to_string_def,comma_cat_word_to_string_ind = define_guess
  `comma_cat_word_to_string x =
    match x with
      [] -> [newl_strlit]
    | [x] -> [word_to_string x; newl_strlit]
    | (CONS x xs) -> CONS (word_to_string x) (CONS comm_strlit
      (comma_cat_word_to_string xs))`;;

(* HOL4 backend_cvScript.sml:1069-1073: ML code, not ported *)

let to_comma_cat_byte_to_string = prove
 (`!xs. comma_cat byte_to_string xs =
        comma_cat_byte_to_string xs`,
  CHEAT_TAC);;

let to_comma_cat_word_to_string = prove
 (`!xs. comma_cat word_to_string xs =
        comma_cat_word_to_string xs`,
  CHEAT_TAC);;

let words_line_byte_def = new_definition
  `words_line_byte word_directive ls =
     misc_List (CONS word_directive (comma_cat_byte_to_string ls))`;;

let words_line_word_def = new_definition
  `words_line_word word_directive ls =
     misc_List (CONS word_directive (comma_cat_word_to_string ls))`;;

(* HOL4 backend_cvScript.sml:1107-1108: ML code, not ported *)

let to_words_line_byte = prove
 (`words_line wd byte_to_string = words_line_byte wd`,
  CHEAT_TAC);;

let to_words_line_word = prove
 (`words_line wd word_to_string = words_line_word wd`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:1124-1128: ML code, not ported *)

(* HOL4 backend_cvScript.sml:1130: ML code, not ported *)

(* [cv_pre] *)
let word_copy_copy_prop_prog_pre = prove
 (`!v cs. word_copy_copy_prop_prog_pre v cs`,
  CHEAT_TAC);;

(* HOL4 backend_cvScript.sml:1140: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id"];;

(* and the interface *)
let _ = unhide_overloads ();;
