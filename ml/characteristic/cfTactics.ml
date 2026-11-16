(* ======================================================== *)
(*  cfTactics: ported from HOL4's
    characteristic/cfTacticsScript.sml
    A definition theory, with no definitions and 18 theorems.  No
    file of the port needs it.  *)
(* ======================================================== *)

(*
  Lemmas that aid the tactics for reasoning about CF-based goals in HOL.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cf.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfHeaps.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfNormalise.ml";;
needs "characteristic/cfStore.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/set_sep.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfTactics"
  ["cf"; "cfApp"; "cfHeaps"; "cfHeapsBase"; "cfNormalise"; "cfStore";
   "ml_translator"];;

let _ = do_list hide_constant ["True"];;

(* HOL4 cfTacticsScript.sml:12-21: code that the source has in a comment *)

let xret_lemma = prove
 (`!H Q R. SEP_IMP H (Q v * GC) /\ R Q ==>
    local (\H' Q'. SEP_IMP H' (Q' v) /\ R Q') H Q`,
  CHEAT_TAC);;

let xret_lemma1 =
  CAKE_GENL [`H`; `Q`] (SIMP_RULE [] (CAKE_SPECL [`H`; `Q`; `K T`]
  xret_lemma));;

(* todo: does it even happen? *)
let xret_lemma_unify = prove
 (`!v H. local (\H' Q'. SEP_IMP H' (Q' v)) H (\x. cond (x = v) * H)`,
  CHEAT_TAC);;

(* HOL4 cfTacticsScript.sml:43-51: code that the source has in a comment *)

let xret_no_gc_lemma = prove
 (`!v H Q R. SEP_IMP H (Q v) /\ R Q ==>
      local (\H' Q'. SEP_IMP H' (Q' v) /\ R Q') H Q`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* Automatic rewrites *)


let INT_Litv = prove
 (`INT i (semanticPrimitives_Litv (ast_IntLit k)) = (i = k)`,
  CHEAT_TAC);;
add_simp INT_Litv;;

let NUM_Litv = prove
 (`NUM n (semanticPrimitives_Litv (ast_IntLit k)) = (k = &n)`,
  CHEAT_TAC);;
add_simp NUM_Litv;;

let CHAR_Litv = prove
 (`CHAR c (semanticPrimitives_Litv (ast_Char c')) = (c = c')`,
  CHEAT_TAC);;
add_simp CHAR_Litv;;

let STRING_Litv = prove
 (`STRING_TYPE s (semanticPrimitives_Litv (ast_StrLit s')) = (s = s')`,
  CHEAT_TAC);;
add_simp STRING_Litv;;

let WORD8_Litv = prove
 (`WORD w (semanticPrimitives_Litv (ast_Word8 w')) = (w = w')`,
  CHEAT_TAC);;
add_simp WORD8_Litv;;

let WORD64_Litv = prove
 (`WORD w (semanticPrimitives_Litv (ast_Word64 w')) = (w = w')`,
  CHEAT_TAC);;
add_simp WORD64_Litv;;

let UNIT_Conv = prove
 (`UNIT_TYPE one (semanticPrimitives_Conv NONE []) = T`,
  CHEAT_TAC);;
add_simp UNIT_Conv;;

let BOOL_T_Conv = prove
 (`BOOL T (semanticPrimitives_Conv (SOME (TypeStamp (implode "True")
  bool_type_num)) []) = T`,
  CHEAT_TAC);;
add_simp BOOL_T_Conv;;

let BOOL_F_Conv = prove
 (`BOOL F (semanticPrimitives_Conv (SOME (TypeStamp (implode "False")
  bool_type_num)) []) = T`,
  CHEAT_TAC);;
add_simp BOOL_F_Conv;;

let BOOL_Boolv = prove
 (`BOOL b (semanticPrimitives_Boolv bv) = (b = bv)`,
  CHEAT_TAC);;
add_simp BOOL_Boolv;;

(*------------------------------------------------------------------*)
(* Used for cleaning up after unfolding [build_cases] (in cf_match) *)

let exists_v_of_pat_norest_length = prove
 (`!envC pat insts v.
     (?insts wildcards. v_of_pat_norest envC pat insts wildcards = SOME v)
       <=>
     (?insts wildcards. LENGTH insts = LENGTH (ast_pat_bindings pat) /\
                        LENGTH wildcards = pat_wildcards pat /\
                        v_of_pat_norest envC pat insts wildcards = SOME v)`,
  CHEAT_TAC);;

let forall_v_of_pat_norest_length = prove
 (`!envC pat insts v P.
     (!insts wildcards. v_of_pat_norest envC pat insts wildcards = SOME v
       ==> P insts) <=>
     (!insts wildcards. LENGTH insts = LENGTH (ast_pat_bindings pat) ==>
                        LENGTH wildcards = pat_wildcards pat ==>
                        v_of_pat_norest envC pat insts wildcards = SOME v
                          ==>
                        P insts)`,
  CHEAT_TAC);;

let BOOL_T =
  CAKE_EVAL [BOOL_def; bvlSem_Boolv_def; bool_to_tag_def; true_tag_def;
  false_tag_def] `BOOL T (semanticPrimitives_Conv (SOME (TypeStamp (implode
  "True") 0)) [])`;;

let BOOL_F =
  CAKE_EVAL [BOOL_def; bvlSem_Boolv_def; bool_to_tag_def; true_tag_def;
  false_tag_def] `BOOL F (semanticPrimitives_Conv (SOME (TypeStamp (implode
  "False") 0)) [])`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["True"];;

(* and the interface *)
let _ = unhide_overloads ();;
