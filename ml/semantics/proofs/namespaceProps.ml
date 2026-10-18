(* ======================================================== *)
(*  namespaceProps: ported from HOL4's
    semantics/proofs/namespacePropsScript.sml  *)
(* ======================================================== *)

(*
  Proofs about the namespace datatype.
*)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;

(* ----------- Monotonicity for ind rel ------------ *)

(* ---------- Automatic simps involving empty envs -------------- *)

(* ------------- Other simple automatic theorems --------- *)

(* -------------- nsLookup ------------------ *)

(* -------------- alist_to_ns --------------- *)

(* -------------- nsLift --------------- *)

(* --------------- nsAppend ------------- *)

(* -------------- nsAll ---------------- *)

(* -------------- nsSub ---------------- *)

let alist_rel_restr_def = cake_define_list
  [`alist_rel_restr R l1 l2 [] <=> T`;
   `alist_rel_restr R l1 l2 (k1 :: keys) <=>
        (match ALOOKUP l1 k1 with NONE -> F | SOME v1 ->
          (match ALOOKUP l2 k1 with NONE -> F | SOME v2 -> R k1
            v1 v2 /\ alist_rel_restr R l1 l2 keys))`];;

let alistSub_def = cake_define
  `alistSub R e1 e2 <=> alist_rel_restr R e1 e2 (MAP FST e1)`;;

(* HOL4 namespacePropsScript.sml:785: ML code, not ported *)

let _ = size_thms "namespace";;
(* HOL4 namespacePropsScript.sml:791-801: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let nsSub_compute_def = cake_define_try_tac (fun () ->
  `MEASURE (\(p,r,env,_1). namespace_size (\x. 0) (\x. 0) (\x. 0) env)`)
  CHEAT_TAC
  `nsSub_compute path' R (Bind e1V e1M) (Bind e2V e2M) <=>
     alistSub (\k v1 v2. R (mk_id (REVERSE path') k) v1 v2) e1V e2V
       /\
     alistSub (\k v1 v2. nsSub_compute (k :: path') R v1 v2) e1M
       e2M`;;

(* HOL4 namespacePropsScript.sml:841-989: code that the source has in
   a comment *)

(* -------------- nsAll2 ---------------- *)

(* -------------- nsMap --------------- *)

(* --------------- nsDom --------------- *)
