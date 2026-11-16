(* ======================================================== *)
(*  ml_monad_translatorBase: ported from HOL4's
    translator/monadic/ml_monad_translatorBaseScript.sml
    A definition theory, with 7 definitions and 58 theorems.  Needed
    by candle_kernel_funs.ml, cfMonad.ml, ml_monadStore.ml and
    ml_monad_translator.ml.  *)
(* ======================================================== *)

(*
  Assertions about references and arrays are defined. Lemmas for these
  are proved, including reasoning in separation logic.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cf.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/patternMatches.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_pmatch.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_monad_translatorBase"
  ["ast"; "cf"; "cfHeapsBase"; "cfStore"; "cfTactics"; "evaluate";
   "ml_monadBase"; "ml_pmatch"; "ml_prog"; "ml_translator";
   "semanticPrimitives"];;

(* HOL4 ml_monad_translatorBaseScript.sml:14: ML code, not ported *)

(* HOL4 ml_monad_translatorBaseScript.sml:16-18: ML code, not ported *)

(* HOL4 ml_monad_translatorBaseScript.sml:20: ML code, not ported *)

(* HOL4 ml_monad_translatorBaseScript.sml:22: the type abbreviation state,
   which the port expands *)

(* a few basics *)
let with_same_refs = prove
 (`(semanticPrimitives_state_refs_fupd (K (semanticPrimitives_state_refs s))
  s) = s`,
  CHEAT_TAC);;

let with_same_ffi = prove
 (`(semanticPrimitives_state_ffi_fupd (K (semanticPrimitives_state_ffi s)) s)
  = s`,
  CHEAT_TAC);;

let with_same_clock = prove
 (`(semanticPrimitives_state_clock_fupd (K (semanticPrimitives_state_clock
  s)) s) = s`,
  CHEAT_TAC);;

(* REF_REL *)
let REF_REL_def = new_definition
  `REF_REL TYPE' r x = SEP_EXISTS (\v. REF r v * &(TYPE' x v))`;;

(* HOL4 ml_monad_translatorBaseScript.sml:48: the ML values that the
   definitions below antiquote *)

(* REFS_PRED *)
let REFS_PRED_def = new_definition
  `REFS_PRED (h,(p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) refs s = (h refs * GC) (st2heap p s)`;;

let VALID_REFS_PRED_def = new_definition
  `VALID_REFS_PRED
  (H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) = (?(s:'ffi semanticPrimitives_state) refs. REFS_PRED H
  refs s)`;;

(* Frame rule for EvalM *)

let REFS_PRED_FRAME_def = new_definition
  `REFS_PRED_FRAME ro (h,(p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) (refs1,s1) (refs2,s2) <=>
     (ro ==> (?refs. s2 = semanticPrimitives_state_refs_fupd (K refs) s1))
       /\ semanticPrimitives_state_next_type_stamp
     s2 = semanticPrimitives_state_next_type_stamp s1
       /\ semanticPrimitives_state_next_exn_stamp
     s2 = semanticPrimitives_state_next_exn_stamp s1 /\
     (!F'. (h refs1 * F') (st2heap p s1) ==> (h refs2 * F' * GC) (st2heap
       p s2))`;;

let EMP_STAR_GC = prove
 (`!H. emp * H = H`,
  CHEAT_TAC);;

let SAT_GC = prove
 (`!h. GC h`,
  CHEAT_TAC);;

let REFS_PRED_FRAME_imp = prove
 (`!refs1 s1 H refs2 s2.
   REFS_PRED
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
     option)) list)) refs1 s1 ==>
   REFS_PRED_FRAME ro H (refs1,s1) (refs2,s2) ==> REFS_PRED H refs2 s2`,
  CHEAT_TAC);;

let REFS_PRED_FRAME_trans = prove
 (`REFS_PRED_FRAME ro
  ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) (refs1,s1) (refs2,s2) ==>
   REFS_PRED_FRAME ro H (refs2,s2) (refs3,s3) ==>
   REFS_PRED_FRAME ro H (refs1,s1) (refs3,s3)`,
  CHEAT_TAC);;

let H_STAR_GC_SAT_IMP = prove
 (`H s ==> (H * GC) s`,
  CHEAT_TAC);;

let REFS_PRED_FRAME_same = prove
 (`!H st s. REFS_PRED_FRAME ro H (st,s) (st,s)`,
  CHEAT_TAC);;

(*
 * Proof of REFS_PRED_APPEND:
 * `REFS_PRED H refs s ==> REFS_PRED H refs (s with refs := s.refs ++ junk)`
 *)
let store2heap_aux_Mem = prove
 (`!s n x. x IN (store2heap_aux n s) ==> (?n' v. x = cfHeapsBase_Mem n' v)`,
  CHEAT_TAC);;

let store2heap_aux_IN_LENGTH = prove
 (`!s r x n. cfHeapsBase_Mem r x IN (store2heap_aux n s) ==> r < n + LENGTH s`,
  CHEAT_TAC);;

(* [local] *)
let NEG_DISJ_TO_IMP = prove
 (`!A B. ~A \/ ~B <=> A /\ B ==> F`,
  CHEAT_TAC);;

let store2heap_aux_DISJOINT = prove
 (`!n s1 s2. DISJOINT (store2heap_aux n s1) (store2heap_aux (n + LENGTH s1)
  s2)`,
  CHEAT_TAC);;

let store2heap_aux_SPLIT = prove
 (`!s1 s2 n. SPLIT (store2heap_aux n (APPEND s1 s2))
                 (store2heap_aux n s1,store2heap_aux (n + LENGTH s1) s2)`,
  CHEAT_TAC);;

let store2heap_DISJOINT = prove
 (`DISJOINT (store2heap s1) (store2heap_aux (LENGTH s1) s2)`,
  CHEAT_TAC);;

(* If the goal is: (\x. P x) = (\x. Q x), applies SUFF_TAC ``!x. P x = Q x`` *)
(* HOL4 ml_monad_translatorBaseScript.sml:190-199: a proof *)

let store2heap_SPLIT = prove
 (`!s1 s2. SPLIT (store2heap (APPEND s1 s2))
                 (store2heap s1,store2heap_aux (LENGTH s1) s2)`,
  CHEAT_TAC);;

let SPLIT_DECOMPOSWAP = prove
 (`SPLIT s1 (s2,s3) ==> SPLIT s2 (u,v) ==> SPLIT s1 (u,v UNION s3)`,
  CHEAT_TAC);;

let STORE_APPEND_JUNK = prove
 (`!H s junk. H (store2heap s) ==> (H * GC) (store2heap (APPEND s junk))`,
  CHEAT_TAC);;

let st2heap_SPLIT_FFI = prove
 (`!f st. SPLIT ((store2heap (semanticPrimitives_state_refs st)) UNION
  (ffi2heap f (semanticPrimitives_state_ffi st)))
                (store2heap (semanticPrimitives_state_refs st),ffi2heap f
                  (semanticPrimitives_state_ffi st))`,
  CHEAT_TAC);;

let SPLIT3_swap12 = prove
 (`!h h1 h2 h3. SPLIT3 h (h1,h2,h3) = SPLIT3 h (h2,h1,h3)`,
  CHEAT_TAC);;

let SPLIT_of_SPLIT3_1u3 = prove
 (`!h h1 h2 h3. SPLIT3 h (h1,h2,h3) ==> SPLIT h (h2,h1 UNION h3)`,
  CHEAT_TAC);;

let SPLIT2_SPLIT3 = prove
 (`SPLIT s1 (s2,t3) /\ SPLIT s2 (t1,t2) ==> SPLIT3 s1 (t1,t2,t3)`,
  CHEAT_TAC);;

let SPLIT_SYM = prove
 (`SPLIT s (s1,s2) = SPLIT s (s2,s1)`,
  CHEAT_TAC);;

let STATE_APPEND_JUNK = prove
 (`!H p s refs junk. H (st2heap p (semanticPrimitives_state_refs_fupd (K refs)
  s)) ==>
   (H * GC) (st2heap p (semanticPrimitives_state_refs_fupd (K (APPEND refs
     junk)) s))`,
  CHEAT_TAC);;

let STATE_SPLIT_REFS = prove
 (`!a b p s. SPLIT (st2heap p (semanticPrimitives_state_refs_fupd (K (APPEND a
  b)) s))
   ((st2heap p (semanticPrimitives_state_refs_fupd (K a)
     s)),(store2heap_aux (LENGTH a) b))`,
  CHEAT_TAC);;

let REFS_PRED_append = prove
 (`!H refs s. REFS_PRED H refs s ==>
              REFS_PRED
                ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
                (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
                cfHeapsBase_ffi_result) option)) list)) refs
                (semanticPrimitives_state_refs_fupd (K (APPEND
                (semanticPrimitives_state_refs s) junk)) s)`,
  CHEAT_TAC);;

let REFS_PRED_qappend = prove
 (`!H refs s.
     REFS_PRED H refs s ==>
     (!junk.
     REFS_PRED H refs (semanticPrimitives_state_refs_fupd (K (APPEND
       (semanticPrimitives_state_refs s) junk)) s))`,
  CHEAT_TAC);;

let REFS_PRED_FRAME_append = prove
 (`!H refs s. REFS_PRED_FRAME ro
  ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) (refs,s) (refs,semanticPrimitives_state_refs_fupd (K
  (APPEND (semanticPrimitives_state_refs s) junk)) s)`,
  CHEAT_TAC);;

(*
 * Proof of STORE_EXTRACT_FROM_HPROP:
 * `!l xv H s. (REF (Loc T l) xv * H) (store2heap s) ==> ?ps. ((ps ++ [Refv xv]) ≼ s) /\ LENGTH ps = l`
 *)

let HEAP_LOC_MEM = prove
 (`(cell l rv * H) h ==> cfHeapsBase_Mem l rv IN h`,
  CHEAT_TAC);;

let st2heap_CELL_MEM = prove
 (`(cell l rv * H) (st2heap p s) ==> cfHeapsBase_Mem l rv IN (store2heap
  (semanticPrimitives_state_refs s))`,
  CHEAT_TAC);;

let st2heap_REF_MEM = prove
 (`(REF (semanticPrimitives_Loc T l) xv * H) (st2heap p s) ==>
  cfHeapsBase_Mem l (semanticPrimitives_Refv xv) IN (store2heap
  (semanticPrimitives_state_refs s))`,
  CHEAT_TAC);;

let st2heap_ARRAY_MEM = prove
 (`(ARRAY (semanticPrimitives_Loc T l) av * H) (st2heap p s) ==>
  cfHeapsBase_Mem l (semanticPrimitives_Varray av) IN (store2heap
  (semanticPrimitives_state_refs s))`,
  CHEAT_TAC);;

let store2heap_aux_LOC_MEM = prove
 (`!l rv H n s. (cell l rv * H) (store2heap_aux n s) ==>
                cfHeapsBase_Mem l rv IN (store2heap_aux n s)`,
  CHEAT_TAC);;

let store2heap_LOC_MEM = prove
 (`!l rv H s. (cell l rv * H) (store2heap s) ==> cfHeapsBase_Mem l rv IN
  (store2heap s)`,
  CHEAT_TAC);;

let isPREFIX_TAKE = prove
 (`!l s. isPREFIX (TAKE l s) s`,
  CHEAT_TAC);;

let isPREFIX_APPEND_EQ = prove
 (`!a1 a2 b1 b2.
     LENGTH a1 = LENGTH a2 ==>
     (isPREFIX (APPEND a1 b1) (APPEND a2 b2) <=> a2 = a1 /\ isPREFIX b1
       b2)`,
  CHEAT_TAC);;

let STATE_DECOMPOS_FROM_HPROP = prove
 (`!l rv H p s. (cell l rv * H) (st2heap p s) ==>
                (?ps. ((APPEND ps [rv]) <<= semanticPrimitives_state_refs
                  s) /\ LENGTH ps = l)`,
  CHEAT_TAC);;

let STATE_DECOMPOS_FROM_HPROP_REF = prove
 (`!l xv H p s. (REF (semanticPrimitives_Loc T l) xv * H) (st2heap p s) ==>
                (?ps. ((APPEND ps [semanticPrimitives_Refv xv]) <<=
                  semanticPrimitives_state_refs s) /\ LENGTH ps = l)`,
  CHEAT_TAC);;

let STATE_DECOMPOS_FROM_HPROP_ARRAY = prove
 (`!l av H p s. (ARRAY (semanticPrimitives_Loc T l) av * H) (st2heap p s) ==>
                (?ps. ((APPEND ps [semanticPrimitives_Varray av]) <<=
                  semanticPrimitives_state_refs s) /\ LENGTH ps = l)`,
  CHEAT_TAC);;

let STATE_EXTRACT_FROM_HPROP = prove
 (`!l rv H p s. (cell l rv * H) (st2heap p s) ==>
   (!junk. EL l (APPEND (semanticPrimitives_state_refs s) junk) = rv)`,
  CHEAT_TAC);;

let STATE_EXTRACT_FROM_HPROP_REF = prove
 (`!l xv H p s. (REF (semanticPrimitives_Loc T l) xv * H) (st2heap p s) ==>
   (!junk. EL l (APPEND (semanticPrimitives_state_refs s) junk) =
     semanticPrimitives_Refv xv)`,
  CHEAT_TAC);;

let STATE_EXTRACT_FROM_HPROP_ARRAY = prove
 (`!l av H p s. (ARRAY (semanticPrimitives_Loc T l) av * H) (st2heap p s) ==>
   (!junk. EL l (APPEND (semanticPrimitives_state_refs s) junk) =
     semanticPrimitives_Varray av)`,
  CHEAT_TAC);;

let SEPARATE_STORE_ELEM_IN_HEAP = prove
 (`!s0 x s1. SPLIT3 (store2heap (APPEND (APPEND s0 [x]) s1))
                    (store2heap s0,{cfHeapsBase_Mem (LENGTH s0) x},
                     store2heap_aux (LENGTH s0 + 1) s1)`,
  CHEAT_TAC);;

let CELL_HPROP_SAT_EQ = prove
 (`!l xv s. (cell l xv) s <=> s = {cfHeapsBase_Mem l xv}`,
  CHEAT_TAC);;

let REF_HPROP_SAT_EQ = prove
 (`!l xv s. REF (semanticPrimitives_Loc T l) xv s <=> s = {cfHeapsBase_Mem l
  (semanticPrimitives_Refv xv)}`,
  CHEAT_TAC);;

let ARRAY_HPROP_SAT_EQ = prove
 (`!l av s. ARRAY (semanticPrimitives_Loc T l) av s <=> s = {cfHeapsBase_Mem
  l (semanticPrimitives_Varray av)}`,
  CHEAT_TAC);;

let SPLIT_UNICITY_R = prove
 (`SPLIT s (u,v) ==> (SPLIT s (u,v') <=> v' = v)`,
  CHEAT_TAC);;

let DIFF_UNION_COMM = prove
 (`DISJOINT s2 s3 ==>
   (s1 UNION s2) DIFF s3 = (s1 DIFF s3) UNION s2`,
  CHEAT_TAC);;

let STATE_SAT_CELL_STAR_H_EQ = prove
 (`!p s s0 rv s1 H.
     (cell (LENGTH s0) rv * H) (st2heap p
       (semanticPrimitives_state_refs_fupd (K (APPEND (APPEND s0 [rv]) s1)) s))
       <=>
     H ((store2heap s0) UNION
       (store2heap_aux (LENGTH s0 + 1) s1) UNION
       (ffi2heap p (semanticPrimitives_state_ffi s)))`,
  CHEAT_TAC);;

let STATE_SAT_REF_STAR_H_EQ = prove
 (`!p s s0 xv s1 H.
     (REF (semanticPrimitives_Loc T (LENGTH s0)) xv * H)
        (st2heap p (semanticPrimitives_state_refs_fupd (K (APPEND (APPEND s0
          [semanticPrimitives_Refv xv]) s1)) s)) <=>
     H ((store2heap s0) UNION
        (store2heap_aux (LENGTH s0 + 1) s1) UNION (ffi2heap p
          (semanticPrimitives_state_ffi s)))`,
  CHEAT_TAC);;

let STATE_SAT_ARRAY_STAR_H_EQ = prove
 (`!p s s0 av s1 H.
     (ARRAY (semanticPrimitives_Loc T (LENGTH s0)) av * H)
        (st2heap p (semanticPrimitives_state_refs_fupd (K (APPEND (APPEND s0
          [semanticPrimitives_Varray av]) s1)) s)) <=>
     H ((store2heap s0) UNION
        (store2heap_aux (LENGTH s0 + 1) s1) UNION (ffi2heap p
          (semanticPrimitives_state_ffi s)))`,
  CHEAT_TAC);;

let STATE_UPDATE_HPROP_CELL = prove
 (`(cell l rv * H) (st2heap p s) ==> (cell l rv' * H)
    (st2heap p (semanticPrimitives_state_refs_fupd (K (LUPDATE rv' l
      (semanticPrimitives_state_refs s))) s))`,
  CHEAT_TAC);;

let STATE_UPDATE_HPROP_REF = prove
 (`(REF (semanticPrimitives_Loc T l) xv * H) (st2heap p s) ==> (REF
  (semanticPrimitives_Loc T l) xv' * H)
     (st2heap p (semanticPrimitives_state_refs_fupd (K (LUPDATE
       (semanticPrimitives_Refv xv') l (semanticPrimitives_state_refs s)))
       s))`,
  CHEAT_TAC);;

let STATE_UPDATE_HPROP_ARRAY = prove
 (`(ARRAY (semanticPrimitives_Loc T l) av * H) (st2heap p s) ==> (ARRAY
  (semanticPrimitives_Loc T l) av' * H)
     (st2heap p (semanticPrimitives_state_refs_fupd (K (LUPDATE
       (semanticPrimitives_Varray av') l (semanticPrimitives_state_refs s)))
       s))`,
  CHEAT_TAC);;

(* HOL4 ml_monad_translatorBaseScript.sml:651-665: code that the source has
   in a comment *)

(* Fixed-size arrays *)
let ARRAY_REL_def = new_definition
  `ARRAY_REL TYPE' rv l = SEP_EXISTS (\av. ARRAY rv av * &(ALL2 TYPE' l av))`;;

(* Resizable arrays *)
let RARRAY_def = new_definition
  `RARRAY rv av = SEP_EXISTS (\arv. REF rv arv * ARRAY arv av)`;;

let RARRAY_REL_def = new_definition
  `RARRAY_REL TYPE' rv l = SEP_EXISTS (\av. RARRAY rv av * &(ALL2 TYPE' l
  av))`;;

let RARRAY_HPROP_SAT_EQ = prove
 (`RARRAY (semanticPrimitives_Loc T l) av s <=>
   (?l'. s = {cfHeapsBase_Mem l' (semanticPrimitives_Varray
     av),cfHeapsBase_Mem l (semanticPrimitives_Refv (semanticPrimitives_Loc T
     l'))})`,
  CHEAT_TAC);;

(* [local] *)
let GC_ABSORB_L = prove
 (`!A B s. (A * B * GC) s ==> (A * GC) s`,
  CHEAT_TAC);;

let st2heap_SPLIT = prove
 (`SPLIT (st2heap ffi (semanticPrimitives_state_refs_fupd (K (APPEND
  (semanticPrimitives_state_refs s) junk)) s))
         (st2heap ffi s,store2heap_aux (LENGTH
           (semanticPrimitives_state_refs s)) junk)`,
  CHEAT_TAC);;

let REFS_PRED_FRAME_remove_junk = prove
 (`REFS_PRED_FRAME ro H (n_st,semanticPrimitives_state_refs_fupd (K (APPEND
  (semanticPrimitives_state_refs s1) junk)) s1) (st2,s2) ==>
   REFS_PRED_FRAME ro H (n_st,s1) (st2,s2)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
