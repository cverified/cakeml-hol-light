(* ======================================================== *)
(*  inferProg: ported from HOL4's
    compiler/bootstrap/translation/inferProgScript.sml
    A definition theory, with 2 definitions and 37 theorems.  Needed
    by explorerProg.ml.  *)
(* ======================================================== *)

(*
  Translate the compiler's type inferencer.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/bootstrap/translation/parserProg.ml";;
needs "compiler/bootstrap/translation/reg_allocProg.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/inferProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "inferProg"
  ["infer"; "inferProps"; "ml_monadBase"; "ml_translator"; "parserProg";
   "reg_allocProg"; "semanticPrimitives"];;

(* HOL4 inferProgScript.sml:11-14: ML code, not ported *)

(* HOL4 inferProgScript.sml:18-19: ML code, not ported *)

(* HOL4 inferProgScript.sml:21: ML code, not ported *)

(* translator setup *)

(* HOL4 inferProgScript.sml:25-35: ML code, not ported *)

(* HOL4 inferProgScript.sml:37: ML code, not ported *)

(* HOL4 inferProgScript.sml:39-40: ML code, not ported *)

(* NOT_NIL_AND_LEMMA *)
let inferProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:48: ML code, not ported *)

(* HOL4 inferProgScript.sml:50-67: ML code, not ported *)

(* HOL4 inferProgScript.sml:69: ML code, not ported *)

(* type inference: t_walkstar and t_unify *)

(* [local] *)
let PRECONDITION_INTRO = prove
 (`(b ==> (x = y)) ==> (x = (if PRECONDITION b then y else x))`,
  CHEAT_TAC);;

let t_vwalk_ind = prove
 (`!P.
      (!s v.
        (!v1 u. FLOOKUP s v = SOME v1 /\ v1 = Infer_Tuvar u ==> P s u) ==>
        P s v) ==>
      (!s v. t_wfs s ==> P s v)`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:93-96: ML code, not ported *)

(* HOL4 inferProgScript.sml:98-109: a theorem that HOL4 states as the value
   of an ML expression: t_vwalk_side_def *)

(* HOL4 inferProgScript.sml:111: ML code, not ported *)

(* t_walkstar_ind *)
let inferProg_t_walkstar_ind = prove
 (`!P.
      (!s t.
         (!ts tc0 a. t_walk s t = Infer_Tapp ts tc0 /\ MEM a ts ==> P s a)
           ==>
         P s t) ==>
      (!s t. t_wfs s ==> P s t)`,
  CHEAT_TAC);;

(* [local] *)
let expand_lemma = prove
 (`t_walkstar s = (\x. t_walkstar s x)`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:129-132: ML code, not ported *)

(* HOL4 inferProgScript.sml:134-145: a theorem that HOL4 states as the value
   of an ML expression: t_walkstar_side_def *)

let t_oc_ind = prove
 (`!P.
      (!s t v.
        (!ts tt a. t_walk s t = Infer_Tapp ts tt /\ MEM a ts ==> P s a v)
          ==>
        P s t v) ==>
      (!s t v. t_wfs s ==> P (s:(num,infer_t)fmap) (t:infer_t) (v:num))`,
  CHEAT_TAC);;

(* [local] *)
let EXISTS_LEMMA = prove
 (`!xs P. EX P xs = EX I (MAP P xs)`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:165-168: ML code, not ported *)

(* HOL4 inferProgScript.sml:170-177: a theorem that HOL4 states as the value
   of an ML expression: t_oc_side_lemma *)

(* HOL4 inferProgScript.sml:179-185: a theorem that HOL4 states as the value
   of an ML expression: t_oc_side_def *)

(* HOL4 inferProgScript.sml:187: ML code, not ported *)

(* HOL4 inferProgScript.sml:189-221: a theorem that HOL4 states as the value
   of an ML expression: t_unify_lemma *)

(* HOL4 inferProgScript.sml:223: ML code, not ported *)

(* HOL4 inferProgScript.sml:225: ML code, not ported *)

(* HOL4 inferProgScript.sml:227-236: a theorem that HOL4 states as the value
   of an ML expression: t_unify_side_lemma *)

(* HOL4 inferProgScript.sml:238-244: a theorem that HOL4 states as the value
   of an ML expression: t_unify_side_def *)

(* HOL4 inferProgScript.sml:246-252: a theorem that HOL4 states as the value
   of an ML expression: ts_unify_side_def *)

(* HOL4 inferProgScript.sml:254-255: ML code, not ported *)

(* HOL4 inferProgScript.sml:257-259: a theorem that HOL4 states as the value
   of an ML expression: anub_ind *)

(* HOL4 inferProgScript.sml:261-263: ML code, not ported *)

(* HOL4 inferProgScript.sml:265-274: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:276-277: ML code, not ported *)

(* [local] *)
let pair_abs_hack = prove
 (`(\((v2:mlstring),(v1:infer_t)). (v2,0,v1)) =
     (\v3. match v3 with (v2,v1) -> (v2,(0:num),v1))`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:286-313: the ML values that the definitions
   below antiquote *)

(* [local] *)
let if_apply = prove
 (`!b. (if b then x1 else x2) x = if b then x1 x else x2 x`,
  CHEAT_TAC);;

(* [local] *)
let option_case_apply = prove
 (`!oo. oo option_CASE (x1 x2 x) = oo option_CASE ((x1 x) (\y. x2 y x))`,
  CHEAT_TAC);;

(* [local] *)
let pr_CASE = prove
 (`pair_CASE (x,y) f = f x y`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:333-341: ML code, not ported *)

(* [local] *)
let list_apply = prove
 (`!op. (list_CASE op x1 x2) y =
          (list_CASE op (x1 y) (\z1 z2. x2 z1 z2 y))`,
  CHEAT_TAC);;

(* Converts PMATCH case expressions applied to an argument, e.g.

     (case x of
       p1 => λ v1. b1 v1
     | p2 => λ v2. b2 v2
     | ....) a

into a case expression with the argument applied in each branch

     case x of
       p1 => b1 a
     | p2 => b2 a
     | ....

*)
(* HOL4 inferProgScript.sml:365-368: ML code, not ported *)

(* HOL4 inferProgScript.sml:370-389: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:391-392: ML code, not ported *)

(* HOL4 inferProgScript.sml:394-395: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:397-398: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:400: ML code, not ported *)

let ty_var_name_eq = prove
 (`ty_var_name n =
     mlvector_concat [(implode "'");
             if n < 28 then mlint_toString (CHR (n + ORD (CHR 97))) else
               mlint_toString (&n)]`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:411: ML code, not ported *)

(* HOL4 inferProgScript.sml:413-418: ML code, not ported *)

(* HOL4 inferProgScript.sml:420: the ML values that the definitions below
   antiquote *)

(* HOL4 inferProgScript.sml:422: ML code, not ported *)

(* HOL4 inferProgScript.sml:424: the ML values that the definitions below
   antiquote *)

let add_constraint_side_thm = prove
 (`!l x y z. t_wfs (infer_st_subst z) ==> add_constraint_side l x y z`,
  CHEAT_TAC);;

let add_constraints_side_thm = prove
 (`!l x y z. t_wfs (infer_st_subst z) ==> add_constraints_side l x y z`,
  CHEAT_TAC);;

(* [local] *)
let LET3_APP = prove
 (`(let (a,b,c) = x in y a b c) z = (let (a,b,c) = x in y a b c z)`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:451-454: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:456: ML code, not ported *)

(* [local] *)
let MAP_type_name_subst = prove
 (`MAP (type_name_subst tenvT) ts =
   MAP (\x. type_name_subst tenvT x) ts`,
  CHEAT_TAC);;

(* [local] *)
let lemma = prove
 (`MAP (\(x,y). foo x y) = MAP (\z. foo (FST z) (SND z))`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:471-473: ML code, not ported *)

(* HOL4 inferProgScript.sml:475-479: a theorem whose statement the port
   cannot state yet: EVERY_INTRO *)

(* [local] *)
let EVERY_EQ_EVERY = prove
 (`!xs. ALL P xs = ALL I (MAP P xs)`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:487-488: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:490-491: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:493: the ML values that the definitions below
   antiquote *)

(* HOL4 inferProgScript.sml:495-497: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:499: the ML values that the definitions below
   antiquote *)

(* HOL4 inferProgScript.sml:501-509: a theorem that HOL4 states as the value
   of an ML expression: inter_p_lemma1 *)

(* HOL4 inferProgScript.sml:511: ML code, not ported *)

(* HOL4 inferProgScript.sml:513-518: a theorem that HOL4 states as the value
   of an ML expression: infer_p_ind *)

(* HOL4 inferProgScript.sml:520: ML code, not ported *)

(* HOL4 inferProgScript.sml:522: ML code, not ported *)

let infer_p_side_thm = prove
 (`(!l cenv p st. t_wfs (infer_st_subst st) ==> infer_p_side l cenv p st) /\
   (!l cenv ps st. t_wfs (infer_st_subst st) ==> infer_ps_side l cenv ps
     st)`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:539: the ML values that the definitions below
   antiquote *)

(* HOL4 inferProgScript.sml:541-555: a theorem that HOL4 states as the value
   of an ML expression: inter_e_lemma1 *)

(* HOL4 inferProgScript.sml:557-564: a theorem that HOL4 states as the value
   of an ML expression: infer_e_ind *)

(* HOL4 inferProgScript.sml:566: ML code, not ported *)

(* HOL4 inferProgScript.sml:568-572: ML code, not ported *)

let infer_e_side_thm = prove
 (`(!l menv e st. t_wfs (infer_st_subst st) ==> infer_e_side l menv e st) /\
   (!l menv es st. t_wfs (infer_st_subst st) ==> infer_es_side l menv es st)
     /\
   (!l menv pes t1 t2 st. t_wfs (infer_st_subst st) ==> infer_pes_side l
     menv pes t1 t2 st) /\
   (!l menv funs st. t_wfs (infer_st_subst st) ==> infer_funs_side l menv
     funs st)`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:624-625: the ML values that the definitions
   below antiquote *)

(* HOL4 inferProgScript.sml:627: ML code, not ported *)

(* [local] *)
let generalise_list_length = prove
 (`!min' start' s x.
     LENGTH x = LENGTH (SND (SND (generalise_list min' start' s (MAP f
       (MAP SND x)))))`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with sum_INL d -> dec_size d
                                   | sum_INR ds -> list_size dec_size ds)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let gen_d_ind_def,gen_d_ind_ind = define_guess
  `(gen_d_ind (Dmod n ds) = gen_ds_ind ds) /\
   (gen_d_ind (Dlocal lds ds) = (gen_ds_ind lds /\ gen_ds_ind ds)) /\
   (gen_d_ind _ = T) /\
   (gen_ds_ind [] = T) /\
   (gen_ds_ind (CONS x xs) = (gen_d_ind x /\ gen_ds_ind xs))`;;

(* HOL4 inferProgScript.sml:650-653: ML code, not ported *)

let infer_d_side_thm = prove
 (`(!d ienv s. t_wfs (infer_st_subst s) ==> infer_d_side ienv d s) /\
   (!ds ienv s. t_wfs (infer_st_subst s) ==> infer_ds_side ienv ds s)`,
  CHEAT_TAC);;

(* [local] *)
let MEM_anub = prove
 (`!e1M ls k v1.
   MEM (k,v1) (anub e1M ls) ==>
   MEM (k,v1) e1M`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (\(p,r,env,_). namespace_size (\x. 0) (\x. 0) (\x. 0) env)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 inferProgScript.sml:692-699: the tactic that proves the termination *)
let nsSub_translate_def,nsSub_translate_ind = define_guess
  `nsSub_translate parmove_path R b1 b2 <=>
   (match b1 with (Bind e1V e1M) -> (match b2 with (Bind e2V e2M) ->
     ALL (\(k,v1).
       match ALOOKUP e2V k with
         NONE -> F
       | SOME v2 -> R (mk_id (REVERSE parmove_path) k) v1 v2) (anub e1V [])
         /\
     ALL (\(k,v1).
       match ALOOKUP e2M k with
         NONE -> F
       | SOME v2 -> nsSub_translate (CONS k parmove_path) R v1 v2) (anub
         e1M [])))`;;

(* [local] *)
let ALOOKUP_MEM_anub = prove
 (`!ls acc k v.
   MEM (k,v) (anub ls acc) <=>
   (ALOOKUP ls k = SOME v /\ ~(MEM k acc))`,
  CHEAT_TAC);;

(* MEM_ALOOKUP[local] *)
let inferProg_MEM_ALOOKUP = prove
 (`!ls k. MEM k (MAP FST ls) ==> (?v. ALOOKUP ls k = SOME v)`,
  CHEAT_TAC);;

(* [local] *)
let nsSub_thm = prove
 (`!ls R e1 e2. nsSub_compute ls R e1 e2 <=> nsSub_translate ls R e1 e2`,
  CHEAT_TAC);;

(* HOL4 inferProgScript.sml:742: ML code, not ported *)

(* HOL4 inferProgScript.sml:744-748: a theorem that HOL4 states as the value
   of an ML expression: infertype_prog_side_thm *)


(* HOL4 inferProgScript.sml:751: ML code, not ported *)

(* HOL4 inferProgScript.sml:753: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
