(* ======================================================== *)
(*  bvi_tmc: ported from HOL4's
    compiler/backend/bvi_tmcScript.sml  *)
(* ======================================================== *)

(*
  Perform tailrec modulo cons optimisation to make more functions
    tail-recursive.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: integer *)

let pure_op_def = cake_define
  `bvi_tmc_pure_op x1 x2 =
        match (x1,x2) with
          ((Label _1),_2) -> F
        | ((FFI _3),_4) -> F
        | ((closLang_IntOp (Const n)),[]) -> small_enough_int n
        | ((closLang_IntOp _5),_6) -> F
        | ((closLang_WordOp _7),_8) -> F
        | ((closLang_BlockOp (Cons _9)),_10) -> T
        | ((closLang_BlockOp _11),_12) -> F
        | ((closLang_GlobOp _13),_14) -> F
        | ((closLang_MemOp _15),_16) -> F
        | (Install,_17) -> F
        | ((ThunkOp _18),_19) -> F`;;
hol4_overload "pure_op" "bvi_tmc_pure_op";;

(* HOL4 termination: *)
let pure_exp_def = cake_define_wf
  `MEASURE (\x. match x with INL (_33,e) -> exp_size e | INR (_34,es)
  -> list_size exp_size es)`
  `(pure_exp n (Var v) = (v < n)) /\
   (pure_exp n (If e1 e2 e3) = F) /\
   (pure_exp n (Let es e) = (pure_exp n e /\ pure_exps n es)) /\
   (pure_exp n (Raise _20) = F) /\
   (pure_exp n (Tick e) = F) /\
   (pure_exp n (Call _21 _22 _23 _24) = F) /\
   (pure_exp n (Force _25 _26) = F) /\
   (pure_exp n (bvi_LetCall _27 _28 _29 _30 _31) = F) /\
   (pure_exp n (Return _32) = F) /\
   (pure_exp n (Op op args) = (pure_op op args /\ pure_exps n args))
     /\
   (pure_exps n [] = T) /\
   (pure_exps n (h :: t) = (pure_exp n h /\ pure_exps n t))`;;

(* The equations below express pure_exps without the auxiliary pure_exp.
    This
   is the shape the ml_translator prefers (cf. bvi_let$compile_def),
     whereas the
   mutually recursive pure_exp_def above is the shape cv_trans requires.
     *)

let dest_Cons_def = cake_define
  `bvi_tmc_dest_Cons x1 =
      match x1 with
        (closLang_BlockOp (Cons block_tag)) -> SOME block_tag
      | _35 -> NONE`;;
hol4_overload "dest_Cons" "bvi_tmc_dest_Cons";;

(* PHASE 1: extract everything into a let bound "call block" *)

(* CallBlock tag left child right
   This is the "skeleton" of the BlockOp Cons
   - with the same tag,
   - where the recursive call is at the bottom of child,
   - where left and right are de Bruijn indeces of the other args,
     positions preserved,
     with the original expressions assumed to be let bound.
 *)
let call_block_INDUCT,call_block_RECURSION = define_datatype
  "call_block = CallBlock (num) (num list) (call_block) (num list) | \
   RCall (num) (num list)";;

let bind_def = cake_define
  `(bind (n:num) [] = ([],n)) /\
   (bind (n:num) (_36 :: t) =
    (match bind (n + 1) t with (vs,n') -> (n :: vs,n')))`;;

let shift_vars_def = cake_define
  `(shift_vars (n:num) [] = []) /\
   (shift_vars (n:num) (h :: t) = (h + (n:num)) :: shift_vars n t)`;;

let shift_cb_def = cake_define
  `(shift_cb n (RCall ts args) = RCall ts (shift_vars n args)) /\
   (shift_cb n (CallBlock tag l c r) =
    (let l' = shift_vars n l in
    let c' = shift_cb n c in
    let r' = shift_vars n r in
      CallBlock tag l' c' r'))`;;

let call_to_cb_def = cake_define
  `call_to_cb loc call_ts call_loc call_args call_h =
   (if call_loc = SOME loc /\ call_h = NONE then
     match bind 0 call_args with (vs,_37) ->
         SOME (call_args,RCall call_ts vs) else NONE)`;;

(* Attempts to build a CallBlock from the tag and args of a BlockOp
   Cons.
   If no recursive call found, returns each op arg expression in a list
     and (INL) a list of corresponding de Bruijn indeces.
   If a recursive call is found, returns all extracted/let-bound
     expressions and (INR) the call block.
   If an effectful operation appears right of the recursive call, the
     expression is not eligible for transformation and NONE is returned.
   If multiple recursive calls are found, all but the last are let
     bound. *)
(* HOL4 termination: *)
let bvi_to_cb_aux_def = cake_define_wf
  `MEASURE (\x. match x with INL (_42,_43,_44,e) -> exp_size e | INR
  (_45,_46,_47,es) -> list_size exp_size es)`
  `bvi_to_cb_aux_sing n loc tag exp =
        match exp with
          (Call t loc' args h) ->
      match call_to_cb loc t loc' args h with SOME (bs,cb) -> SOME
        (bs,INR (CallBlock tag [] cb [])) | _38 -> NONE
        | (Op op args) ->
      match dest_Cons op with SOME tag' ->
          (match bvi_to_cb_aux n loc tag' args with NONE -> NONE |
            SOME (bs,INL vs) ->
               (if pure_exp n (Op op args) then
                 SOME ([Op op args],INL [0]) else NONE) | SOME
                   (bs,INR cb) ->
               SOME (bs,INR (CallBlock tag [] cb []))) | NONE ->
          (if pure_exp n (Op op args) then
            SOME ([Op op args],INL [0]) else NONE)
        | exp ->
      if pure_exp n exp then
        SOME ([exp],INL [0]) else NONE
        | [] -> SOME ([],INL [])
        | [exp] -> bvi_to_cb_aux_sing n loc tag exp
        | (h :: t) ->
      match bvi_to_cb_aux n loc tag t with NONE -> NONE | SOME
        (bs2,INL vs2) ->
          (match bvi_to_cb_aux_sing n loc tag h with NONE -> NONE |
            SOME (bs1,INL vs1) ->
               (if small_enough_int (&(LENGTH vs1 + LENGTH vs2)) then
                 let vs2' = shift_vars (LENGTH bs1) vs2 in
                   SOME (bs1 ++ bs2,INL (vs1 ++ vs2')) else NONE) |
                     SOME (bs1,INR (CallBlock _39 [] child [])) ->
               (let vs2' = shift_vars (LENGTH bs1) vs2 in
                 SOME (bs1 ++ bs2,INR (CallBlock tag [] child vs2')))
                   | _40 -> NONE) | SOME (bs2,INR cb) ->
          (match shift_cb 1 cb with CallBlock tag l child r ->
              (let cb' = CallBlock tag (0 :: l) child r in
                SOME (h :: bs2,INR cb')) | _41 -> NONE)`;;

let wf_vars_def = cake_define
  `wf_vars n (vs:num list) <=> EVERY (\v. v < n) vs`;;

let wf_cb_def = cake_define
  `(wf_cb n (RCall ts args) =
    wf_vars n args) /\
   (wf_cb n (CallBlock tag left child right) =
    (wf_vars n left /\
     wf_cb n child /\
     wf_vars n right /\
     small_enough_int (&LENGTH right)))`;;

let bvi_to_cb_def = cake_define
  `bvi_to_cb n loc x3 =
        match x3 with
          (Call call_ts call_loc call_args call_h) ->
      call_to_cb loc call_ts call_loc call_args call_h
        | (Op op xs) ->
      match dest_Cons op with SOME tag ->
          (match bvi_to_cb_aux n loc tag xs with SOME (bs,INR cb) ->
            SOME (bs,cb) | _48 -> NONE) | _49 -> NONE
        | _50 -> NONE`;;

(* Convert back to BlockOp Cons for comparing semantics *)
let cb_to_bvi_def = cake_define
  `(cb_to_bvi loc (CallBlock tag l child r) =
      (let l' = MAP (\n. Var n) l in
      let child' = cb_to_bvi loc child in
      let r' = MAP (\n. Var n) r in
        Op (closLang_BlockOp (Cons tag)) (l' ++ [child'] ++ r'))) /\
   (cb_to_bvi loc (RCall ts args) =
      (let args' = MAP (\n. Var n) args in
        bvi_Call ts (SOME loc) args' NONE))`;;

(* Phase 2 - Transformations. *)

let mut_cons_def = cake_define
  `mut_cons t l r =
     (let l' = MAP (\n. Var n) l in
     let hole' = Op (closLang_IntOp (Const 0)) [] in
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
  `optimise_call call_ts loc_opt call_args exp_ptr exp_idx =
   (let args = MAP (\n. Var n) call_args ++ [exp_ptr; exp_idx] in
     Call call_ts (SOME loc_opt) args NONE)`;;

let update_cons_def = cake_define
  `update_cons exp_ptr exp_idx exp_val = Op (closLang_MemOp
  closLang_UpdateCons) [exp_val; exp_idx; exp_ptr]`;;

let cb_size_def = cake_define
  `cb_size x1 =
      match x1 with
        (CallBlock _51 _52 x _53) -> cb_size x + 1
      | _54 -> 0`;;

(* HOL4 termination: \\ rw [call_block_size_shift, cb_size_def] *)
let cb_to_bvi_worker_aux_def = cake_define_wf
  `MEASURE (cb_size o FST)`
  `(cb_to_bvi_worker_aux (RCall call_ts call_args) loc_opt ptr idx =
    optimise_call call_ts loc_opt call_args (Var ptr) (Op
      (closLang_IntOp (Const (&idx))) [])) /\
   (cb_to_bvi_worker_aux (CallBlock tag left child right) loc_opt ptr
     idx =
    Let [mut_cons tag left right] (
    Let [update_cons (Var (ptr + 1)) (Op (closLang_IntOp (Const
      (&idx))) []) (Var 0)]
      (cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1 (LENGTH
        right))))`;;

(* Same as cb_to_bvi_worker_aux, but with the shift carried as an
   accumulator
   so that the recursion is on a subterm of the call block.  This
     version is
   the one used by the cv translation. *)
let cb_to_bvi_worker_aux_alt_def = cake_define
  `(cb_to_bvi_worker_aux_alt sh (RCall call_ts call_args) loc_opt ptr
  idx =
    optimise_call call_ts loc_opt (shift_vars sh call_args) (Var ptr)
      (Op (closLang_IntOp (Const (&idx))) [])) /\
   (cb_to_bvi_worker_aux_alt sh (CallBlock tag left child right)
     loc_opt ptr idx =
    Let [mut_cons tag (shift_vars sh left) (shift_vars sh right)] (
    Let [update_cons (Var (ptr + 1)) (Op (closLang_IntOp (Const
      (&idx))) []) (Var 0)]
      (cb_to_bvi_worker_aux_alt (sh + 2) child loc_opt 1 (LENGTH
        right))))`;;

let cb_to_bvi_worker_def = cake_define
  `(cb_to_bvi_worker (RCall call_ts call_args) loc_opt ptr idx =
    optimise_call call_ts loc_opt call_args (Var ptr) (Var idx)) /\
   (cb_to_bvi_worker (CallBlock tag left child right) loc_opt ptr idx
     =
    Let [mut_cons tag left right] (
        Let [update_cons (Var (ptr + 1)) (Var (idx + 1)) (Var 0)]
        (cb_to_bvi_worker_aux (shift_cb 2 child) loc_opt 1 (LENGTH
          right))))`;;

let cb_to_bvi_wrapper_def = cake_define
  `(cb_to_bvi_wrapper tag left child right loc_opt =
    Let [mut_cons tag left right] (
        Let [cb_to_bvi_worker_aux (shift_cb 1 child) loc_opt 0
          (LENGTH right)]
        (finalise_cons 1)))`;;

(* Expression rewriting *)
let rewrite_wrapper_def = cake_define
  `rewrite_wrapper loc loc_opt n x4 =
        match x4 with
          (Var n) -> NONE
        | (If xi xt xe) ->
       let opt_t = rewrite_wrapper loc loc_opt n xt in
       let opt_e = rewrite_wrapper loc loc_opt n xe in
       match (opt_t,opt_e) with (NONE,NONE) -> NONE | (SOME yt,NONE)
         -> SOME (If xi yt xe) | (NONE,SOME ye) -> SOME (If xi xt ye) |
         (SOME yt,SOME ye) -> SOME (If xi yt ye)
        | (Let xs x) ->
       match rewrite_wrapper loc loc_opt (n + LENGTH xs) x with NONE
         -> NONE | SOME y -> SOME (Let xs y)
        | (Raise x) -> NONE
        | (Tick x) -> OPTION_MAP Tick (rewrite_wrapper loc loc_opt n
          x)
        | (Force _55 n) -> NONE
        | (Call t d args h) -> NONE
        | (Op op op_args) ->
       match bvi_to_cb n loc (Op op op_args) with SOME (bs,CallBlock
         tag left child right) ->
           SOME (Let bs (cb_to_bvi_wrapper tag left child right
             loc_opt)) | _56 -> NONE
        | _57 -> NONE`;;

(* Assumes that the function can and should be optimised - has been
   checked by rewrite_wrapper. *)
let rewrite_worker_def = cake_define
  `rewrite_worker loc loc_opt i_old_ptr i_old_idx n expr =
        match expr with
          (If xi xt xe) ->
       let yt = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xt
         in
       let ye = rewrite_worker loc loc_opt i_old_ptr i_old_idx n xe
         in
       If xi yt ye
        | (Let xs x) ->
       let offset = LENGTH xs in
         Let xs (rewrite_worker loc loc_opt (i_old_ptr + offset)
           (i_old_idx + offset) (n + offset) x)
        | (Raise x) -> Raise x
        | (Op op op_args) ->
      match bvi_to_cb n loc (Op op op_args) with SOME (bs,cb) ->
          (let offset = LENGTH bs in
             Let bs (cb_to_bvi_worker cb loc_opt (offset + i_old_ptr)
               (offset + i_old_idx))) | NONE ->
          fill_hole i_old_ptr i_old_idx (Op op op_args)
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

let compile_exp_def = cake_define
  `bvi_tmc_compile_exp (loc:num) (next:num) (arity:num) (exp:bvi_exp) =
     (match rewrite_wrapper loc next arity exp with NONE -> NONE |
       SOME exp_wrapper ->
       (let exp_worker = rewrite_worker loc next arity (arity + 1)
         arity exp in
       SOME (exp_wrapper,exp_worker)))`;;
hol4_overload "compile_exp" "bvi_tmc_compile_exp";;

let compile_each_def = cake_define
  `(bvi_tmc_compile_each next [] = (next,[])) /\
   (bvi_tmc_compile_each next ((loc,arity,exp) :: xs) =
     (match compile_exp loc next arity exp with NONE ->
         (let (n,ys) = bvi_tmc_compile_each next xs in
           (n,(loc,arity,exp) :: ys)) | SOME (exp_wrapper,exp_worker)
             ->
         (let (n,ys) = bvi_tmc_compile_each (next +
           bvl_to_bvi_namespaces) xs in
         (n,(loc,arity,exp_wrapper) :: (next,arity + 2,exp_worker)
           :: ys))))`;;
hol4_overload "compile_each" "bvi_tmc_compile_each";;

let compile_prog_def = cake_define
  `bvi_tmc_compile_prog do_it next xs =
     (if do_it then compile_each next xs else (next,xs))`;;
hol4_overload "compile_prog" "bvi_tmc_compile_prog";;
