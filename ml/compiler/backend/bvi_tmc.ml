(* ======================================================== *)
(*  bvi_tmc: ported from HOL4's
    compiler/backend/bvi_tmcScript.sml
    A definition theory, with 27 definitions, 1 datatype and 33
    theorems.  Needed by bvi_tmcProof.ml and bvl_to_bvi.ml.  *)
(* ======================================================== *)

(*
  Perform tailrec modulo cons optimisation to make more functions tail-recursive.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: integer *)

let bvi_tmc_pure_op_def = cake_define
  `bvi_tmc_pure_op x1 x2 =
        match (x1,x2) with
          ((closLang_Label _2:closLang_op),_3) -> F
        | ((FFI _4),_5) -> F
        | ((closLang_IntOp (closLang_Const n)),[]) ->
          small_enough_int n
        | ((closLang_IntOp _6),_7) -> F
        | ((closLang_WordOp _8),_9) -> F
        | ((closLang_BlockOp (closLang_Cons _10)),_11) -> T
        | ((closLang_BlockOp _12),_13) -> F
        | ((closLang_GlobOp _14),_15) -> F
        | ((closLang_MemOp _16),_17) -> F
        | (closLang_Install,_18) -> F
        | ((ThunkOp _19),_20) -> F`;;
hol4_overload "pure_op" "bvi_tmc_pure_op";;

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let pure_exp_def = cake_define_list_try (fun () ->
  `MEASURE (\x. match x with INL (_42,e) -> bvi_exp_size e | INR
     (_43,es) -> list_size bvi_exp_size es)`)
  [`pure_exp n (Var v:bvi_exp) = (v < n)`;
   `pure_exp n (If e1 e2 e3:bvi_exp) = F`;
   `pure_exp n (Let es e:bvi_exp) = (pure_exp n e /\ pure_exps n es)`;
   `pure_exp n (Raise _22:bvi_exp) = F`;
   `pure_exp n (Tick e:bvi_exp) = F`;
   `pure_exp n (Call _27 _28 _29 _30:bvi_exp) = F`;
   `pure_exp n (Force _33 _34:bvi_exp) = F`;
   `pure_exp n (bvi_LetCall _35 _36 _37 _38 _39) = F`;
   `pure_exp n (bvi_Return _41:bvi_exp) = F`;
   `pure_exp n (Op op args:bvi_exp) = (pure_op op args /\ pure_exps n
  args)`;
   `pure_exps n [] = T`;
   `pure_exps n (h :: t) = (pure_exp n h /\ pure_exps n t)`];;

(* [simp] *)
let pure_exps_sing = prove
 (`!n h. pure_exps n [h] <=> pure_exp n h`,
  CHEAT_TAC);;

let pure_exps_cons = prove
 (`!n h t.
     pure_exps n [h] /\
     pure_exps n t <=>
     pure_exps n (h :: t)`,
  CHEAT_TAC);;

(* The equations below express pure_exps without the auxiliary pure_exp.  This
   is the shape the ml_translator prefers (cf. bvi_let$compile_def), whereas the
   mutually recursive pure_exp_def above is the shape cv_trans requires. *)
let pure_exps_eqns = prove
 (`(pure_exps n [] <=> T) /\
   (pure_exps n [bvi_Var v] <=> v < n) /\
   (pure_exps n [bvi_If e1 e2 e3] <=> F) /\
   (pure_exps n [bvi_Let les le] <=> pure_exps n [le] /\ pure_exps n
     les) /\
   (pure_exps n [bvi_Raise re] <=> F) /\
   (pure_exps n [bvi_Tick te] <=> F) /\
   (pure_exps n [bvi_Call ct cd cargs ch] <=> F) /\
   (pure_exps n [bvi_Force fl fw] <=> F) /\
   (pure_exps n [bvi_LetCall la lb lc largs lce] <=> F) /\
   (pure_exps n [bvi_Return res] <=> F) /\
   (pure_exps n [bvi_Op oop oargs] <=> pure_op oop oargs /\ pure_exps
     n oargs) /\
   (pure_exps n (x1 :: x2 :: xs) <=> pure_exps n [x1] /\ pure_exps
     n (x2 :: xs))`,
  CHEAT_TAC);;

let pure_exp_eq = prove
 (`!n e. pure_exp n e = pure_exps n [e]`,
  CHEAT_TAC);;

let pure_exps_append = prove
 (`!n es1 es2.
     pure_exps n es1 /\
     pure_exps n es2 ==>
     pure_exps n (es1 ++ es2)`,
  CHEAT_TAC);;

let dest_Cons_def = cake_define
  `bvi_tmc_dest_Cons x1 =
      match x1 with
        closLang_BlockOp (closLang_Cons block_tag) -> SOME block_tag
      | _44 -> NONE`;;
hol4_overload "dest_Cons" "bvi_tmc_dest_Cons";;

(* PHASE 1: extract everything into a let bound "call block" *)

(* CallBlock tag left child right
   This is the "skeleton" of the BlockOp Cons
   - with the same tag,
   - where the recursive call is at the bottom of child,
   - where left and right are de Bruijn indeces of the other args, positions preserved,
     with the original expressions assumed to be let bound.
 *)
let call_block_INDUCT,call_block_RECURSION = define_datatype
  "call_block = CallBlock (num) (num list) (call_block) (num list) | \
   RCall (num) (num list)";;

let bind_def = cake_define_list
  [`bvi_tmc_bind (n:num) [] = ([],n)`;
   `bvi_tmc_bind (n:num) (_45 :: t) =
       (match bvi_tmc_bind (n + 1) t with (vs,n') -> (n ::
         vs,n'))`];;
hol4_overload "bind" "bvi_tmc_bind";;

let bind_size = prove
 (`!args n vs n'.
     bvi_tmc_bind n args = (vs,n') ==>
     LENGTH args = LENGTH vs`,
  CHEAT_TAC);;

let shift_vars_def = cake_define_list
  [`shift_vars (n:num) [] = []`;
   `shift_vars (n:num) (h :: t) = (h + (n:num)) :: shift_vars n t`];;

let shift_cb_def = cake_define_list
  [`shift_cb n (RCall ts args) = RCall ts (shift_vars n args)`;
   `shift_cb n (CallBlock tag l c r) =
       (let l' = shift_vars n l in
       let c' = shift_cb n c in
       let r' = shift_vars n r in
         CallBlock tag l' c' r')`];;

let call_to_cb_def = cake_define
  `call_to_cb loc call_ts call_loc call_args' call_h =
   (if call_loc = SOME loc /\ call_h = NONE then
     match bvi_tmc_bind 0 call_args' with (vs,_46) ->
         SOME (call_args',RCall call_ts vs) else NONE)`;;

let shift_vars_zero = prove
 (`!ns.
     shift_vars 0 ns = ns`,
  CHEAT_TAC);;

let length_shift_vars = prove
 (`!l n.
      LENGTH (shift_vars n l) = LENGTH l`,
  CHEAT_TAC);;

let shift_vars_dist = prove
 (`!l n1 n2.
     shift_vars n1 (shift_vars n2 l) = shift_vars (n1 + n2) l`,
  CHEAT_TAC);;

let shift_cb_dist = prove
 (`!cb n1 n2.
     shift_cb n1 (shift_cb n2 cb) =
     shift_cb (n1 + n2) cb`,
  CHEAT_TAC);;

(* Attempts to build a CallBlock from the tag and args of a BlockOp Cons.
   If no recursive call found, returns each op arg expression in a list and (INL) a list of corresponding de Bruijn indeces.
   If a recursive call is found, returns all extracted/let-bound expressions and (INR) the call block.
   If an effectful operation appears right of the recursive call, the expression is not eligible for transformation and NONE is returned.
   If multiple recursive calls are found, all but the last are let bound. *)
let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let bvi_to_cb_aux_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\x. match x with INL (_58,_59,_60,e) -> bvi_exp_size e |
     INR (_61,_62,_63,es) -> list_size bvi_exp_size es)`)
  CHEAT_TAC
  [`bvi_to_cb_aux_sing n loc tag (Call t loc' args h:bvi_exp) =
       (match call_to_cb loc t loc' args h with SOME (bs,cb) ->
         SOME (bs,INR (CallBlock tag [] cb [])) | _49 -> NONE)`;
   `bvi_to_cb_aux_sing n loc tag (Op op args:bvi_exp) =
       (match bvi_tmc_dest_Cons op with SOME tag' ->
           (
            // BlockOp Cons - try to recurse
            match bvi_to_cb_aux n loc tag' args with NONE -> NONE |
              SOME (bs,INL vs) ->
                // No recursive call - whole thing gets let-bound
                (if pure_exp n (Op op args) then
                  SOME ([Op op args],INL [0]) else NONE) | SOME
                    (bs,INR cb) ->
                // Recursive call - inductive case of CallBlock
                SOME (bs,INR (CallBlock tag [] cb []))) | NONE ->
           // Not a BlockOp Cons - whole thing gets let-bound
           (if pure_exp n (Op op args) then
             SOME ([Op op args],INL [0]) else NONE))`;
   `bvi_to_cb_aux_sing n _50 _51 exp =
       // Some other expression - whole thing gets let-bound
       (if pure_exp n exp then
         SOME ([exp],INL [0]) else NONE)`;
   `bvi_to_cb_aux _52 _53 _54 [] = SOME ([],INL [])`;
   `bvi_to_cb_aux n loc tag [exp] = bvi_to_cb_aux_sing n loc tag exp`;
   `bvi_to_cb_aux n loc tag (h :: t) =
       // Recurse right to left to find last occurence of recursive call
       (match bvi_to_cb_aux n loc tag t with NONE -> NONE | SOME
         (bs2,INL vs2) ->
           (
            // No recursive call to the right. See if the first has one.
            match bvi_to_cb_aux_sing n loc tag h with NONE -> NONE |
              SOME (bs1,INL vs1) ->
                // No recursive call, keep building binders.
                (if small_enough_int (&(LENGTH vs1 + LENGTH vs2))
                  then
                  let vs2' = shift_vars (LENGTH bs1) vs2 in
                    SOME (bs1 ++ bs2,INL (vs1 ++ vs2')) else NONE) |
                      SOME (bs1,INR (CallBlock _55 [] child [])) ->
                // We've constructed a CallBlock at this level with just h, pad the other args
                // l and r are always empty if args is a singleton
                (let vs2' = shift_vars (LENGTH bs1) vs2 in
                  SOME (bs1 ++ bs2,INR (CallBlock tag [] child
                    vs2'))) | _56 -> NONE) | SOME (bs2,INR cb) ->
           // Recursive call found, first is let bound and added to the left
           (match shift_cb 1 cb with CallBlock tag l child r ->
               (let cb' = CallBlock tag (0 :: l) child r in
                 SOME (h :: bs2,INR cb')) | _57 -> NONE))`];;

let wf_vars_def = cake_define
  `wf_vars n (vs:num list) <=> EVERY (\v. v < n) vs`;;

let wf_vars_empty = prove
 (`!n.
     wf_vars n []`,
  CHEAT_TAC);;

let wf_vars_expand = prove
 (`!n1 n2 vs.
     wf_vars n1 vs /\
     n1 <= n2 ==>
     wf_vars n2 vs`,
  CHEAT_TAC);;

let wf_vars_shift = prove
 (`!n1 n2 vs.
     wf_vars n1 vs ==>
     wf_vars (n2 + n1) (shift_vars n2 vs)`,
  CHEAT_TAC);;

let wf_vars_shift_sing = prove
 (`!n vs.
     wf_vars n vs ==>
     wf_vars (SUC n) (shift_vars 1 vs)`,
  CHEAT_TAC);;

let wf_vars_append = prove
 (`!n vs1 vs2.
     wf_vars n vs1 /\
     wf_vars n vs2 ==>
     wf_vars n (vs1 ++ vs2)`,
  CHEAT_TAC);;

let wf_vars_cons = prove
 (`!n v vs.
     v < n /\
     wf_vars n vs ==>
     wf_vars n (v :: vs)`,
  CHEAT_TAC);;

let wf_vars_bind = prove
 (`!bs vs n n'.
     bvi_tmc_bind n bs = (vs,n') ==>
     wf_vars (n + LENGTH bs) vs`,
  CHEAT_TAC);;

let wf_cb_def = cake_define_list
  [`wf_cb n (RCall ts args) =
       wf_vars n args`;
   `wf_cb n (CallBlock tag left child right) =
       (wf_vars n left /\
        wf_cb n child /\
        wf_vars n right /\
        small_enough_int (&(LENGTH right)))`];;

let wf_cb_expand = prove
 (`!n1 n2 cb.
     wf_cb n1 cb /\
     n1 <= n2 ==>
     wf_cb n2 cb`,
  CHEAT_TAC);;

let wf_cb_shift_sing = prove
 (`!n cb.
     wf_cb n cb ==>
     wf_cb (SUC n) (shift_cb 1 cb)`,
  CHEAT_TAC);;

(* [local] *)
let bvi_to_cb_aux_wf_inl_lemma = prove
 (`(!n loc tag exp bs vs.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ==>
      pure_exps n bs /\
      wf_vars (LENGTH bs) vs /\
      small_enough_int (&(LENGTH vs))) /\
   (!n loc tag args bs vs.
      bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ==>
      pure_exps n bs /\
      wf_vars (LENGTH bs) vs /\
      small_enough_int (&(LENGTH vs)))`,
  CHEAT_TAC);;

(* HOL4 bvi_tmcScript.sml:443: a theorem that HOL4 states as the
   value of an ML expression: bvi_to_cb_aux_wf_inl *)

let bvi_to_cb_aux_sing = prove
 (`!n loc tag arg bs cb.
     bvi_to_cb_aux n loc tag [arg] = SOME (bs,INR cb) ==>
     (?child.
       cb = CallBlock tag [] child [])`,
  CHEAT_TAC);;

(* [local] *)
let bvi_to_cb_aux_wf_inr_lemma = prove
 (`(!n loc tag exp bs cb.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INR cb) ==>
      wf_cb (LENGTH bs) cb /\
      (?l child r.
        cb = CallBlock tag l child r)) /\
   (!n loc tag args bs cb.
      bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) ==>
      wf_cb (LENGTH bs) cb /\
      (?l child r.
        cb = CallBlock tag l child r))`,
  CHEAT_TAC);;

(* HOL4 bvi_tmcScript.sml:490: a theorem that HOL4 states as the
   value of an ML expression: bvi_to_cb_aux_wf_inr *)

let bvi_to_cb_def = cake_define
  `bvi_to_cb n loc x3 =
        match x3 with
          (Call call_ts call_loc call_args' call_h:bvi_exp) ->
      call_to_cb loc call_ts call_loc call_args' call_h
        | (Op op xs) ->
      (match bvi_tmc_dest_Cons op with SOME tag ->
          (match bvi_to_cb_aux n loc tag xs with SOME (bs,INR cb) ->
            SOME (bs,cb) | _64 -> NONE) | _65 -> NONE)
        | _66 -> NONE`;;

let bvi_to_cb_wf = prove
 (`!n loc x bs cb.
     bvi_to_cb n loc x = SOME (bs,cb) ==>
     wf_cb (LENGTH bs) cb`,
  CHEAT_TAC);;

let bvi_to_cb_cases = prove
 (`!n loc x bs cb.
     bvi_to_cb n loc x = SOME (bs,cb) ==>
     (?tag args l child r.
        x = Op (closLang_BlockOp (closLang_Cons tag)) args /\
        cb = CallBlock tag l child r) \/
     (?ts args vs.
        x = Call ts (SOME loc) args NONE /\
        cb = RCall ts vs)`,
  CHEAT_TAC);;

(* Convert back to BlockOp Cons for comparing semantics *)
let cb_to_bvi_def = cake_define_list
  [`cb_to_bvi loc (CallBlock tag l child r) =
         (let l' = MAP (\n. Var n) l in
         let child' = cb_to_bvi loc child in
         let r' = MAP (\n. Var n) r in
           Op (closLang_BlockOp (closLang_Cons tag)) (l' ++
             [child'] ++ r'))`;
   `cb_to_bvi loc (RCall ts args) =
         (let args' = MAP (\n. Var n) args in
           bvi_Call ts (SOME loc) args' NONE)`];;

(* [local] *)
let bvi_to_cb_aux_size_lemma = prove
 (`(!n loc tag exp bs sum'.
      bvi_to_cb_aux_sing n loc tag exp = SOME (bs,sum') ==>
      list_size bvi_exp_size bs <= bvi_exp_size exp + 1) /\
   (!n loc tag args bs sum'.
      bvi_to_cb_aux n loc tag args = SOME (bs,sum') ==>
      list_size bvi_exp_size bs <= list_size bvi_exp_size args)`,
  CHEAT_TAC);;

(* HOL4 bvi_tmcScript.sml:577: a theorem that HOL4 states as the
   value of an ML expression: bvi_to_cb_aux_size *)

let bvi_to_cb_size = prove
 (`!n loc x bs cb.
     bvi_to_cb n loc x = SOME (bs,cb) ==>
     list_size bvi_exp_size bs < bvi_exp_size x`,
  CHEAT_TAC);;

(* Phase 2 - Transformations. *)

let mut_cons_def = cake_define
  `mut_cons t l r =
     (let l' = MAP (\n. Var n) l in
     let hole' = Op (closLang_IntOp (closLang_Const (&0))) [] in
     let r' = MAP (\n. Var n) r in
     let i = LENGTH r in
     Op (closLang_MemOp (closLang_MutCons t i)) (l' ++ [hole'] ++
       r'))`;;

let finalise_cons_def = cake_define
  `bvi_tmc_finalise_cons i_top_ptr = Op (closLang_MemOp
  closLang_FinaliseCons) [Var i_top_ptr]`;;
hol4_overload "finalise_cons" "bvi_tmc_finalise_cons";;

let fill_hole_def = cake_define
  `fill_hole i_ptr i_idx exp = Op (closLang_MemOp
  closLang_UpdateCons) [exp; Var i_idx; Var i_ptr]`;;

let optimise_call_def = cake_define
  `optimise_call call_ts loc_opt call_args' exp_ptr exp_idx =
   (let args = MAP (\n. Var n) call_args' ++ [exp_ptr; exp_idx] in
     Call call_ts (SOME loc_opt) args NONE)`;;

let update_cons_def = cake_define
  `update_cons exp_ptr exp_idx exp_val = Op (closLang_MemOp
  closLang_UpdateCons) [exp_val; exp_idx; exp_ptr]`;;

let cb_size_def = cake_define
  `cb_size x1 =
      match x1 with
        CallBlock _67 _68 x _69 -> cb_size x + 1
      | _70 -> 0`;;

(* [local] *)
let call_block_size_shift = prove
 (`!x n. cb_size (shift_cb n x) = cb_size x`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_tmcScript.sml:644-647: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let cb_to_bvi_worker_aux_def = cake_define_list_try_tac (fun () ->
  `MEASURE (cb_size o FST)`)
  CHEAT_TAC
  [`cb_to_bvi_worker_aux (RCall call_ts call_args') loc_opt ptr idx =
       optimise_call call_ts loc_opt call_args' (Var ptr) (Op
         (closLang_IntOp (closLang_Const (&idx))) [])`;
   `cb_to_bvi_worker_aux (CallBlock tag left child right) loc_opt ptr
  idx =
       Let [mut_cons tag left right] (
       Let [update_cons (Var (ptr + 1)) (Op (closLang_IntOp
         (closLang_Const (&idx))) []) (Var 0)]
         (cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1
           (LENGTH right)))`];;

let shift_cb_zero = prove
 (`!x. shift_cb 0 x = x`,
  CHEAT_TAC);;

(* Same as cb_to_bvi_worker_aux, but with the shift carried as an accumulator
   so that the recursion is on a subterm of the call block.  This version is
   the one used by the cv translation. *)
let cb_to_bvi_worker_aux_alt_def = cake_define_list
  [`cb_to_bvi_worker_aux_alt sh (RCall call_ts call_args') loc_opt ptr
  idx =
       optimise_call call_ts loc_opt (shift_vars sh call_args') (Var
         ptr)
         (Op (closLang_IntOp (closLang_Const (&idx))) [])`;
   `cb_to_bvi_worker_aux_alt sh (CallBlock tag left child right) loc_opt
  ptr idx =
       Let [mut_cons tag (shift_vars sh left) (shift_vars sh right)]
         (
       Let [update_cons (Var (ptr + 1)) (Op (closLang_IntOp
         (closLang_Const (&idx))) []) (Var 0)]
         (cb_to_bvi_worker_aux_alt (sh + 2) child loc_opt 1
           (LENGTH right)))`];;

let cb_to_bvi_worker_aux_alt_thm = prove
 (`!cb sh loc_opt ptr idx.
     cb_to_bvi_worker_aux_alt sh cb loc_opt ptr idx =
     cb_to_bvi_worker_aux (shift_cb sh cb) loc_opt ptr idx`,
  CHEAT_TAC);;

let cb_to_bvi_worker_aux_eq = prove
 (`cb_to_bvi_worker_aux cb loc_opt ptr idx =
   cb_to_bvi_worker_aux_alt 0 cb loc_opt ptr idx`,
  CHEAT_TAC);;

let cb_to_bvi_worker_def = cake_define_list
  [`cb_to_bvi_worker (RCall call_ts call_args') loc_opt ptr idx =
       optimise_call call_ts loc_opt call_args' (Var ptr) (Var
         idx)`;
   `cb_to_bvi_worker (CallBlock tag left child right) loc_opt ptr idx =
       Let [mut_cons tag left right] (
           Let [update_cons (Var (ptr + 1)) (Var (idx + 1)) (Var 0)]
           (cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1
             (LENGTH right)))`];;

let cb_to_bvi_wrapper_def = cake_define
  `(cb_to_bvi_wrapper tag left child right loc_opt =
    Let [mut_cons tag left right] (
        Let [cb_to_bvi_worker_aux (shift_cb 1 child) loc_opt 0
          (LENGTH right)]
        (bvi_tmc_finalise_cons 1)))`;;

(* Expression rewriting *)
let rewrite_wrapper_def = cake_define
  `rewrite_wrapper loc loc_opt n x4 =
        match x4 with
          (Var n:bvi_exp) -> NONE
        | (If xi xt xe) ->
       (let opt_t = rewrite_wrapper loc loc_opt n xt in
       let opt_e = rewrite_wrapper loc loc_opt n xe in
       match (opt_t,opt_e) with (NONE,NONE) -> NONE | (SOME yt,NONE)
         -> SOME (If xi yt xe) | (NONE,SOME ye) -> SOME (If xi xt ye) |
         (SOME yt,SOME ye) -> SOME (If xi yt ye))
        | (Let xs x) ->
       (match rewrite_wrapper loc loc_opt (n + LENGTH xs) x with NONE
         -> NONE | SOME y -> SOME (Let xs y))
        | (Raise x) -> NONE
        | (Tick x) -> OPTION_MAP Tick (rewrite_wrapper loc loc_opt n
          x)
        | (Force _71 n) -> NONE
        | (Call t d args h) -> NONE
        | (Op op op_args) ->
       (match bvi_to_cb n loc (Op op op_args) with SOME (bs,CallBlock
         tag left child right) ->
           SOME (Let bs (cb_to_bvi_wrapper tag left child right
             loc_opt)) | _72 -> NONE)
        | _73 -> NONE`;;

(* Assumes that the function can and should be optimised - has been checked by rewrite_wrapper. *)
let rewrite_worker_def = cake_define
  `rewrite_worker loc loc_opt i_old_ptr i_old_idx n expr =
        match expr with
          (If xi xt xe:bvi_exp) ->
       (let yt = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xt
         in
       let ye = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xe
         in
       If xi yt ye)
        | (Let xs x) ->
       (let offset = LENGTH xs in
         Let xs (rewrite_worker loc loc_opt (i_old_ptr + offset)
           (i_old_idx + offset) (n + offset) x))
        | (Raise x) -> Raise x
        | (Op op op_args) ->
      (match bvi_to_cb n loc (Op op op_args) with SOME (bs,cb) ->
          (let offset = LENGTH bs in
             Let bs (cb_to_bvi_worker cb loc_opt (offset + i_old_ptr)
               (offset + i_old_idx))) | NONE ->
          fill_hole i_old_ptr i_old_idx (Op op op_args))
        | (Tick x) ->
       Tick (rewrite_worker loc loc_opt i_old_ptr i_old_idx n x)
        | (Call ts l args h) ->
      (match bvi_to_cb n loc (Call ts l args h) with SOME (bs,cb) ->
           (let offset = LENGTH bs in
              Let bs (cb_to_bvi_worker cb loc_opt (offset +
                i_old_ptr) (offset + i_old_idx))) | NONE ->
           fill_hole i_old_ptr i_old_idx (Call ts l args h))
        | expr ->
      fill_hole i_old_ptr i_old_idx expr`;;

let bvi_tmc_compile_exp_def = cake_define
  `bvi_tmc_compile_exp (loc:num) (next':num) (arity:num) (exp:bvi_exp) =
     (match rewrite_wrapper loc next' arity exp with NONE -> NONE |
       SOME exp_wrapper ->
       (let exp_worker = rewrite_worker loc next' arity (arity + 1)
         arity exp in
       SOME (exp_wrapper,exp_worker)))`;;
hol4_overload "compile_exp" "bvi_tmc_compile_exp";;

let bvi_tmc_compile_each_def = cake_define_list
  [`bvi_tmc_compile_each next' [] = (next',[])`;
   `bvi_tmc_compile_each next' ((loc,arity,exp) :: xs) =
        (match bvi_tmc_compile_exp loc next' arity exp with NONE ->
            (let (n,ys) = bvi_tmc_compile_each next' xs in
              (n,(loc,arity,exp) :: ys)) | SOME
                (exp_wrapper,exp_worker) ->
            (let (n,ys) = bvi_tmc_compile_each (next' +
              bvl_to_bvi_namespaces) xs in
            (n,(loc,arity,exp_wrapper) :: (next',arity +
              2,exp_worker) :: ys)))`];;
hol4_overload "compile_each" "bvi_tmc_compile_each";;

let bvi_tmc_compile_prog_def = cake_define
  `bvi_tmc_compile_prog do_it next' xs =
     (if do_it then bvi_tmc_compile_each next' xs else (next',xs))`;;
hol4_overload "compile_prog" "bvi_tmc_compile_prog";;
