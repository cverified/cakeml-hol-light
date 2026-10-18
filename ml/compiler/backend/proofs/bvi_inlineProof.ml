(* ======================================================== *)
(*  bvi_inlineProof: ported from HOL4's
    compiler/backend/proofs/bvi_inlineProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness of the CPR worker-wrapper BVI inliner. The cache [cs] is
  persistent across incremental compilation: a cache hit causes the
  matching call to be inlined, and cache entries are trusted only when
  their bodies and arities agree with the compiled code table.
*)

needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

let cache_code_labels_def = cake_define
  `cache_code_labels (cs:(num#bvi_exp) spt) =
     BIGUNION (set_of_list (MAP (bviProps_get_code_labels o SND)
       (sptree_toList cs)))`;;

(* [exp_rel c] relates a source expression to its image under the
   inlining
   phase, where [c] is the transformed target code table.
   [exp_rel_inline] is the only rule that removes a Call boundary. *)
let exp_rel = cake_inductive
  `((!c n. bvi_inlineProof_exp_rel c (Var n) (Var n))) /\
   ((!c loc n. bvi_inlineProof_exp_rel c (Force loc n) (Force loc
     n))) /\
   ((!c x1 x2 x3 y1 y2 y3.
        bvi_inlineProof_exp_rel c x1 y1 /\ bvi_inlineProof_exp_rel c
          x2 y2 /\ bvi_inlineProof_exp_rel c x3 y3 ==>
        bvi_inlineProof_exp_rel c (If x1 x2 x3) (If y1 y2 y3))) /\
   ((!c xs ys x y.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\
          bvi_inlineProof_exp_rel c x y ==>
        bvi_inlineProof_exp_rel c (Let xs x) (Let ys y))) /\
   ((!c x y. bvi_inlineProof_exp_rel c x y ==>
     bvi_inlineProof_exp_rel c (Raise x) (Raise y))) /\
   ((!c x y. bvi_inlineProof_exp_rel c x y ==>
     bvi_inlineProof_exp_rel c (Tick x) (Tick y))) /\
   ((!c op xs ys. LIST_REL (bvi_inlineProof_exp_rel c) xs ys ==>
        bvi_inlineProof_exp_rel c (Op op xs) (Op op ys))) /\
   ((!c ticks dest xs ys handler handler1.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\ OPTREL
          (bvi_inlineProof_exp_rel c) handler handler1 ==>
        bvi_inlineProof_exp_rel c (bvi_Call ticks dest xs handler)
          (bvi_Call ticks dest ys handler1))) /\
   ((!c rets ticks dest xs ys x y.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\
          bvi_inlineProof_exp_rel c x y ==>
        bvi_inlineProof_exp_rel c (bvi_LetCall rets ticks dest xs x)
          (bvi_LetCall rets ticks dest ys y))) /\
   ((!c xs ys. LIST_REL (bvi_inlineProof_exp_rel c) xs ys ==>
        bvi_inlineProof_exp_rel c (bvi_Return xs) (bvi_Return ys)))
          /\
   ((!c ticks n xs ys arity body.
        LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\ sptree_lookup n
          c = SOME (arity,body) /\
        LENGTH ys = arity ==>
        bvi_inlineProof_exp_rel c (bvi_Call ticks (SOME n) xs NONE)
          (Let ys (bvi_mk_tick (SUC ticks) body))))`;;
hol4_overload "exp_rel" "bvi_inlineProof_exp_rel";;

let in_cc_def = cake_define
  `bvi_inlineProof_in_cc cc =
     (\(cs,cfg) prog.
        let (cs1,prog1) = inline_all cs prog in
          match cc cfg prog1 with NONE -> NONE | SOME
            (code,data,cfg1) -> SOME (code,data,(cs1,cfg1)))`;;
hol4_overload "in_cc" "bvi_inlineProof_in_cc";;

let in_co_def = cake_define
  `bvi_inlineProof_in_co co =
     (\n.
        let ((cs,cfg),prog) = co n in
        let (cs1,prog1) = inline_all cs prog in
          (cfg,prog1))`;;
hol4_overload "in_co" "bvi_inlineProof_in_co";;

let in_state_rel_def = cake_define
  `bvi_inlineProof_in_state_rel s (t:('c,'ffi)bviSem_state) <=>
  state_refs
     t = state_refs s /\ state_clock
     t = state_clock s /\ bviSem_state_global
     t = bviSem_state_global s /\ state_ffi
     t = state_ffi s /\ compile_oracle
     t = bvi_inlineProof_in_co (compile_oracle s) /\
     subspt (FST (FST (compile_oracle s 0))) (state_code t) /\
       compile
     s = bvi_inlineProof_in_cc (compile t) /\
     domain (state_code t) = domain (state_code s) /\
     (!k arity exp.
        sptree_lookup k (state_code s) = SOME (arity,exp) ==>
        (?exp1. sptree_lookup k (state_code t) = SOME (arity,exp1) /\
               bvi_inlineProof_exp_rel (state_code t) exp exp1))`;;
hol4_overload "in_state_rel" "bvi_inlineProof_in_state_rel";;

(* Inversion of [exp_rel] on each source constructor. [~inline] is why
   the
   Call clause has a second disjunct. *)

(* The inlined form of a Call evaluates exactly like the Call it
   replaces:
   the extra environment entries are unreachable, and the two differ on
     a
   [Ret]-raise only, which the side condition excludes. *)

(* HOL4 bvi_inlineProofScript.sml:877-907: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:910-912: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:915-936: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:939-955: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:958-972: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:975-989: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:992-1011: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:1014-1028: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:1031-1044: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:1047-1137: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1139-1198: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:1201: ML code, not ported *)

let clean_prog_def = cake_define
  `clean_prog prog =
     MAP (\(name,arity,body). (name,arity,remove_ticks_exp body))
       prog`;;

let remove_ticks_cc_def = cake_define
  `bvi_inlineProof_remove_ticks_cc cc = (\cfg prog. cc cfg
  (clean_prog prog))`;;
hol4_overload "remove_ticks_cc" "bvi_inlineProof_remove_ticks_cc";;

let remove_ticks_co_def = cake_define
  `bvi_inlineProof_remove_ticks_co = (I ## clean_prog)`;;
hol4_overload "remove_ticks_co" "bvi_inlineProof_remove_ticks_co";;

let remove_state_rel_def = cake_define
  `remove_state_rel (s:('c,'ffi)bviSem_state) (t:('c,'ffi)bviSem_state)
  <=> state_refs
     t = state_refs s /\ state_clock t = state_clock s /\
       bviSem_state_global t = bviSem_state_global s /\ state_ffi t =
       state_ffi s /\ state_code
     t = sptree_map (I ## remove_ticks_exp) (state_code s) /\
       compile_oracle
     t = bvi_inlineProof_remove_ticks_co o compile_oracle s /\
       compile
     s = bvi_inlineProof_remove_ticks_cc (compile t)`;;

(* HOL4 bvi_inlineProofScript.sml:1362-1366: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1368-1394: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1396-1418: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1420-1432: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1434-1443: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1445-1523: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1525-1552: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1554-1580: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1582-1655: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:1658-1671: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1673-1677: ML code, not ported *)

(* HOL4 bvi_inlineProofScript.sml:1679-1715: ML code, not ported *)


(* HOL4 bvi_inlineProofScript.sml:1718: ML code, not ported *)
