(* ======================================================== *)
(*  bvl_inlineProof: ported from HOL4's
    compiler/backend/proofs/bvl_inlineProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_inline
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "lib/sptree.ml";;

(* removal of ticks *)

let state_rel_def = cake_define
  `bvl_inlineProof_state_rel (s:('c,'ffi)bvlSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     t = compile_oracle_fupd (K ((I ##
       MAP (I ## I ## (\x. HD (remove_ticks [x])))) o compile_oracle
         s)) (compile_fupd (K (compile t)) (state_code_fupd (K
         (sptree_map (I ## (\x. HD (remove_ticks [x]))) (state_code s)))
         s)) /\ compile
     s = (\cfg prog. compile t cfg
                    (MAP (I ## I ## (\x. HD (remove_ticks [x])))
                      prog))`;;
hol4_overload "state_rel" "bvl_inlineProof_state_rel";;

(* HOL4 bvl_inlineProofScript.sml:25: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:27-28: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:290-294: ML code, not ported *)

let remove_ticks_cc_def = cake_define
  `bvl_inlineProof_remove_ticks_cc cc =
     (\cfg prog'.
          cc cfg (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks
            [x]))) prog'))`;;
hol4_overload "remove_ticks_cc" "bvl_inlineProof_remove_ticks_cc";;

let remove_ticks_co_def = cake_define
  `bvl_inlineProof_remove_ticks_co =
     (I ## MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))))`;;
hol4_overload "remove_ticks_co" "bvl_inlineProof_remove_ticks_co";;

(* HOL4 bvl_inlineProofScript.sml:329-331: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:563-566: ML code, not ported *)

(* correctness of tick_inline *)

let exp_rel = cake_inductive
  `(!cs v. bvl_inlineProof_exp_rel (cs:(num#bvl_exp) spt) [bvl_Var v]
  [bvl_Var v]) /\
   (!cs. bvl_inlineProof_exp_rel cs [] []) /\
   (!cs x x1 xs y y1 ys.
      bvl_inlineProof_exp_rel cs [x] [y] /\
      bvl_inlineProof_exp_rel cs (x1 :: xs) (y1 :: ys) ==>
      bvl_inlineProof_exp_rel cs (x :: x1 :: xs) (y :: y1 :: ys)) /\
   (bvl_inlineProof_exp_rel cs [x1] [y1] /\
    bvl_inlineProof_exp_rel cs [x2] [y2] /\
    bvl_inlineProof_exp_rel cs [x3] [y3] ==>
    bvl_inlineProof_exp_rel cs [bvl_If x1 x2 x3] [bvl_If y1 y2 y3])
      /\
   (bvl_inlineProof_exp_rel cs xs ys /\
    bvl_inlineProof_exp_rel cs [x] [y] ==>
    bvl_inlineProof_exp_rel cs [bvl_Let xs x] [bvl_Let ys y]) /\
   (bvl_inlineProof_exp_rel cs [x1] [y1] /\
    bvl_inlineProof_exp_rel cs [x2] [y2] ==>
    bvl_inlineProof_exp_rel cs [bvl_Handle x1 x2] [bvl_Handle y1 y2])
      /\
   (bvl_inlineProof_exp_rel cs [x] [y] ==>
    bvl_inlineProof_exp_rel cs [bvl_Raise x] [bvl_Raise y]) /\
   (bvl_inlineProof_exp_rel cs [x] [y] ==>
    bvl_inlineProof_exp_rel cs [bvl_Tick x] [bvl_Tick y]) /\
   (bvl_inlineProof_exp_rel cs xs ys ==>
    bvl_inlineProof_exp_rel cs [bvl_Op op xs] [bvl_Op op ys]) /\
   (bvl_inlineProof_exp_rel cs [bvl_Force loc n] [bvl_Force loc n])
     /\
   (bvl_inlineProof_exp_rel cs xs ys ==>
    bvl_inlineProof_exp_rel cs [bvl_Call ticks dest xs] [bvl_Call
      ticks dest ys]) /\
   (bvl_inlineProof_exp_rel cs xs ys /\ sptree_lookup n cs = SOME
     (arity,x) /\
    bvl_inlineProof_exp_rel cs [x] [y] ==>
    bvl_inlineProof_exp_rel cs [bvl_Call ticks (SOME n) xs]
               [bvl_Let ys (mk_tick (SUC ticks) y)])`;;
hol4_overload "exp_rel" "bvl_inlineProof_exp_rel";;

let in_cc_def = cake_define
  `bvl_inlineProof_in_cc limit' cc =
     (\(cs,cfg) prog.
         let (cs1,prog1) = tick_compile_prog limit' cs prog in
           match cc cfg prog1 with NONE -> NONE | SOME
             (code,data,cfg1) -> SOME (code,data,(cs1,cfg1)))`;;
hol4_overload "in_cc" "bvl_inlineProof_in_cc";;

let in_state_rel_def = cake_define
  `bvl_inlineProof_in_state_rel limit' s t <=> state_globals
     t = state_globals s /\ state_refs
     t = state_refs s /\ state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\ compile_oracle
     t = (\n.
       let ((cs,cfg),progs) = compile_oracle s n in
       let (cs1,progs) = tick_compile_prog limit' cs progs in
         (cfg,progs)) /\
     subspt (FST (FST (compile_oracle s 0))) (state_code t) /\
       compile
     s = bvl_inlineProof_in_cc limit' (compile t) /\
     domain (state_code t) = domain (state_code s) /\
     (!k arity exp.
        sptree_lookup k (state_code s) = SOME (arity,exp) ==>
        (?exp2. sptree_lookup k (state_code t) = SOME (arity,exp2) /\
               bvl_inlineProof_exp_rel (state_code s) [exp]
                 [exp2]))`;;
hol4_overload "in_state_rel" "bvl_inlineProof_in_state_rel";;

(* HOL4 bvl_inlineProofScript.sml:641-649: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:663-669: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:671-674: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:676-685: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:737-742: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:751-758: ML code, not ported *)

let in_co_def = cake_define
  `bvl_inlineProof_in_co limit' co = (\n.
       (let
          ((cs,cfg),progs) = co n in let
          (cs1,progs) = tick_compile_prog limit' cs progs in
          (cfg,progs)))`;;
hol4_overload "in_co" "bvl_inlineProof_in_co";;

(* HOL4 bvl_inlineProofScript.sml:1077-1088: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1090-1142: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1144-1158: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1160-1186: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1188-1202: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1204-1413: ML code, not ported *)

(* let_op *)

let let_opt_def = cake_define
  `let_opt split_seq cut_size (arity,prog) =
     (arity,compile_any split_seq cut_size arity (let_op_sing
       prog))`;;

let let_state_rel_def = cake_define
  `let_state_rel split_seq cut_size (s:('c,'ffi)bvlSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     t = compile_oracle_fupd (K ((I ##
       MAP (I ## let_opt split_seq cut_size)) o compile_oracle s))
         (compile_fupd (K (compile t)) (state_code_fupd (K (sptree_map
         (let_opt split_seq cut_size) (state_code s))) s)) /\ compile
     s = (\cfg prog. compile t cfg (MAP (I ## let_opt split_seq
       cut_size) prog))`;;

(* HOL4 bvl_inlineProofScript.sml:1432: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1434-1435: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1444-1447: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1449-1466: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1468-1474: ML code, not ported *)

let let_op_cc_def = cake_define
  `let_op_cc q4 l4 cc =
      (\cfg prog. cc cfg (MAP (I ## let_opt q4 l4) prog))`;;

(* HOL4 bvl_inlineProofScript.sml:1670-1869: ML code, not ported *)

(* combined theorems *)

(* HOL4 bvl_inlineProofScript.sml:1873-1876: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1878-1881: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1883-1889: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1891-1897: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1899-1901: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1903-1909: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1911-1920: ML code, not ported *)

let let_opt_remove_def = cake_define
  `let_opt_remove b l (arity,prog) =
     let_opt b l (arity,HD (remove_ticks [prog]))`;;

(* HOL4 bvl_inlineProofScript.sml:1927-1931: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1939-1942: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1944-1947: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1949-1959: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1961-1964: ML code, not ported *)

let bvl_inline_cc_def = cake_define
  `bvl_inline_cc limit' q4 l4 cc =
     (bvl_inlineProof_in_cc limit'
       (bvl_inlineProof_remove_ticks_cc (let_op_cc q4 l4 cc)))`;;

let bvl_inline_co_def = cake_define
  `bvl_inline_co limit' q4 l4 co =
    (\x. (I ## MAP (I ## let_opt q4 l4))
           (bvl_inlineProof_remove_ticks_co (bvl_inlineProof_in_co
             limit' co x)))`;;

(* HOL4 bvl_inlineProofScript.sml:1977-1982: ML code, not ported *)
