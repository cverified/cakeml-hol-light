(* ======================================================== *)
(*  bvi_tailrecProof: ported from HOL4's
    compiler/backend/proofs/bvi_tailrecProofScript.sml
    A proof theory about bvi_tailrec.ml, with 9 definitions and 85
    theorems.  Needed by bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_tailrec
*)

needs "basis/pure/mlvector.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

let _ = do_list hide_constant ["all"];;

(* TODO

   - It should be possible to prove that we can replace the simplified
     compile_exp by the old compile_exp without touching the evaluate-
     theorem. Benefits:
       * Less code duplication
       * Can inline auxiliary calls more easily
*)

(* HOL4 bvi_tailrecProofScript.sml:22-25: ML code, not ported *)

(* [simp] *)
let get_bin_args_SOME = prove
 (`!exp q.
    get_bin_args exp = SOME q <=>
    (?e1 e2 op. q = (e1,e2) /\ exp = Op op [e1; e2])`,
  CHEAT_TAC);;

(* [simp] *)
let opbinargs_SOME = prove
 (`!exp opr.
   opbinargs opr exp = SOME q <=> ~(opr = bvi_tailrec_Noop) /\ (?x
     y. q = (x,y) /\ exp = Op (to_op opr) [x; y])`,
  CHEAT_TAC);;

(* [simp] *)
let decide_ty_simp1 = prove
 (`(decide_ty ty1 ty2 = Int <=> ty1 = Int /\ ty2 = Int) /\
   (decide_ty ty1 ty2 = List <=> ty1 = List /\ ty2 = List)`,
  CHEAT_TAC);;

(* [simp] *)
let list_to_v_simp = prove
 (`!xs. bvlSem_v_to_list (list_to_v xs) = SOME xs`,
  CHEAT_TAC);;

(* [simp] *)
let to_op_11 = prove
 (`to_op op1 = to_op op2 <=> op1 = op2`,
  CHEAT_TAC);;

(* [simp] *)
let to_op_eq_simp = prove
 (`(to_op x = closLang_IntOp closLang_Add <=> (x = bvi_tailrec_Plus)) /\
   (to_op x = closLang_IntOp closLang_Mult <=> (x =
     bvi_tailrec_Times)) /\
   (to_op x = closLang_IntOp closLang_Mod <=> (x = bvi_tailrec_Noop))
     /\
   (to_op x = closLang_BlockOp ListAppend <=> (x = Append)) /\
   (closLang_IntOp closLang_Add = to_op x <=> (x = bvi_tailrec_Plus))
     /\
   (closLang_IntOp closLang_Mult = to_op x <=> (x =
     bvi_tailrec_Times)) /\
   (closLang_BlockOp ListAppend = to_op x <=> (x = Append)) /\
   (closLang_IntOp closLang_Mod = to_op x <=> (x =
     bvi_tailrec_Noop))`,
  CHEAT_TAC);;

(* [simp] *)
let op_eq_simp = prove
 (`(op_eq bvi_tailrec_Plus x <=> (?xs. x = Op (closLang_IntOp
  closLang_Add) xs)) /\
   (op_eq bvi_tailrec_Times x <=> (?xs. x = Op (closLang_IntOp
     closLang_Mult) xs)) /\
   (op_eq Append x <=> (?xs. x = Op (closLang_BlockOp ListAppend)
     xs))`,
  CHEAT_TAC);;

(* [simp] *)
let scan_expr_EVERY_SING = prove
 (`EVERY P (scan_expr ts loc [x]) <=> P (HD (scan_expr ts loc [x]))`,
  CHEAT_TAC);;

(* [simp] *)
let try_update_LENGTH = prove
 (`LENGTH (try_update ty idx ts) = LENGTH ts`,
  CHEAT_TAC);;

(* [simp] *)
let update_context_LENGTH = prove
 (`LENGTH (update_context ty ts x y) = LENGTH ts`,
  CHEAT_TAC);;

(* [simp] *)
let decide_ty_simp = prove
 (`decide_ty ty1 ty2 = ty3 /\ ~(ty3 = bvi_tailrec_Any) <=>
   ty1 = ty3 /\ ty2 = ty3 /\ ~(ty3 = bvi_tailrec_Any)`,
  CHEAT_TAC);;

let ty_rel_def = cake_define
  `ty_rel = LIST_REL
     (\v t. (t = Int ==> (?k. v = bvlSem_Number k)) /\
            (t = List ==> (?ys. bvlSem_v_to_list v = SOME ys)))`;;

(* HOL4 bvi_tailrecProofScript.sml:120-122: ML code, not ported *)

let list_to_v_imp = prove
 (`!x xs. bvlSem_v_to_list x = SOME xs ==> list_to_v xs = x`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecProofScript.sml:133-135: ML code, not ported *)

let term_ok_int_SING = prove
 (`!ts exp env ((s:('c,'ffi)bviSem_state)) r t.
     term_ok_int ts exp /\
     ty_rel env ts /\
     evaluate ([exp],env,s) = (r,t) ==>
       s = t /\
       (?v. r = Rval [v] /\
       (!((s:('c,'ffi)bviSem_state)). evaluate ([exp],env,s) = (r,s))
         /\
       (?k. v = bvlSem_Number k))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecProofScript.sml:171-175: a proof *)

let term_ok_any_SING = prove
 (`(!ts list' exp env ((s:('c,'ffi)bviSem_state)) r t.
     term_ok_any ts list' exp /\
     ty_rel env ts /\
     evaluate ([exp],env,s) = (r,t) ==>
       s = t /\
       (?v. r = Rval [v] /\
       (!((s:('c,'ffi)bviSem_state)). evaluate ([exp],env,s) = (r,s))
         /\
       (list' ==> (?ys. bvlSem_v_to_list v = SOME ys))))`,
  CHEAT_TAC);;

let term_ok_SING = prove
 (`!ts ty exp env ((s:('c,'ffi)bviSem_state)) r t.
     term_ok ts ty exp /\
     ty_rel env ts /\
     evaluate ([exp],env,s) = (r,t) ==>
       s = t /\
       (?v. r = Rval [v] /\
       (!((s:('c,'ffi)bviSem_state)). evaluate ([exp],env,s) = (r,s))
         /\
       (match ty with
         Int -> (?k. v = bvlSem_Number k) | List -> (?ys.
           bvlSem_v_to_list v = SOME ys) | _1 -> T))`,
  CHEAT_TAC);;

let op_id_val_def = cake_define_list
  [`op_id_val bvi_tailrec_Plus = bvlSem_Number (&0)`;
   `op_id_val bvi_tailrec_Times = bvlSem_Number (&1)`;
   `op_id_val (Append:assoc_op) = bvlSem_Block nil_tag []`;
   `op_id_val bvi_tailrec_Noop = bvlSem_Number (&6333)`];;

let scan_expr_not_Noop = prove
 (`!exp ts loc tt ty r ok op.
     scan_expr ts loc [exp] = [(tt,ty,r,SOME op)] ==> ~(op =
       bvi_tailrec_Noop)`,
  CHEAT_TAC);;

let bvi_tailrecProof_env_rel_def = cake_define
  `bvi_tailrecProof_env_rel ty opt acc env1 env2 <=>
     isPREFIX env1 env2 /\
     (opt ==>
       LENGTH env1 = acc /\
       LENGTH env2 > acc /\
       (match ty with
         Int -> (?k. EL acc env2 = bvlSem_Number k) | List ->
           (?ys. bvlSem_v_to_list (EL acc env2) = SOME ys) |
           bvi_tailrec_Any -> F))`;;
hol4_overload "env_rel" "bvi_tailrecProof_env_rel";;

(* HOL4 bvi_tailrecProofScript.sml:274: the overload in_ns_2, which
   the port expands *)

let bvi_tailrecProof_code_rel_def = cake_define
  `bvi_tailrecProof_code_rel c1 c2 <=>
     (!loc arity exp op.
       sptree_lookup loc c1 = SOME (arity,exp) ==>
       (check_exp loc arity exp = NONE ==>
         sptree_lookup loc c2 = SOME (arity,exp)) /\
       (check_exp loc arity exp = SOME op ==>
         (?n.
           !exp_aux exp_opt.
           compile_exp loc n arity exp = SOME (exp_aux,exp_opt) ==>
             sptree_lookup loc c2 = SOME (arity,exp_aux) /\
             sptree_lookup n c2 = SOME (arity + 1,exp_opt))))`;;
hol4_overload "code_rel" "bvi_tailrecProof_code_rel";;

(* [local] *)
let code_rel_find_code_SOME = prove
 (`!c1 c2 (args:bvlSem_v list) a exp.
      bvi_tailrecProof_code_rel c1 c2 /\
      find_code (SOME n) args c1 = SOME (a,exp) ==> ~(find_code
        (SOME n) args c2 = NONE)`,
  CHEAT_TAC);;

(* [local] *)
let code_rel_find_code_NONE = prove
 (`!c1 c2 (args:bvlSem_v list) a exp.
      bvi_tailrecProof_code_rel c1 c2 /\
      find_code NONE args c1 = SOME (a,exp) ==> ~(find_code NONE
        args c2 = NONE)`,
  CHEAT_TAC);;

let code_rel_domain = prove
 (`!c1 c2.
     bvi_tailrecProof_code_rel c1 c2 ==> domain c1 SUBSET domain c2`,
  CHEAT_TAC);;

let evaluate_let_wrap = prove
 (`!x op vs ((s:('c,'ffi)bviSem_state)) r t. ~(op = bvi_tailrec_Noop)
  ==>
     evaluate ([let_wrap (LENGTH vs) (id_from_op op) x],vs,s) =
     evaluate ([x],vs ++ [op_id_val op] ++ vs,s)`,
  CHEAT_TAC);;

let evaluate_complete_ind = prove
 (`!P.
    (!xs s.
      (!ys t.
        list_size bvi_exp_size ys < list_size bvi_exp_size xs /\
          state_clock
        t <= bviSem_state_clock s \/ state_clock t <
          bviSem_state_clock s ==>
        P ys t) ==>
      P xs s) ==>
    (!(xs:bvi_exp list) ((s:(num#'c,'ffi)bviSem_state)). P xs s)`,
  CHEAT_TAC);;

let EVERY_LAST1 = prove
 (`!xs y. EVERY P xs /\ LAST1 xs = SOME y ==> P y`,
  CHEAT_TAC);;

let scan_expr_LENGTH = prove
 (`!ts loc xs ys.
     scan_expr ts loc xs = ys ==>
       EVERY (\y. LENGTH (FST y) = LENGTH ts) ys`,
  CHEAT_TAC);;

let ty_rel_decide_ty = prove
 (`!ts tt env.
     (ty_rel env ts \/ ty_rel env tt) /\ LENGTH ts = LENGTH tt ==>
       ty_rel env (MAP2 decide_ty ts tt)`,
  CHEAT_TAC);;

(* [local] *)
let ty_rel_APPEND = prove
 (`!env ts ws vs.
      ty_rel env ts /\ ty_rel vs ws ==> ty_rel (vs ++ env) (ws ++
        ts)`,
  CHEAT_TAC);;

let LAST1_thm = prove
 (`!xs. LAST1 xs = NONE <=> xs = []`,
  CHEAT_TAC);;

let try_update_EL = prove
 (`n < LENGTH ts ==>
   EL n (try_update ty idx ts) =
     (match idx with
       NONE -> EL n ts | SOME m ->
         (if n < m then
           EL n ts else if n > m then
           EL n ts else if EL n ts = bvi_tailrec_Any \/ EL n ts = ty
             then
           ty else
           EL n ts))`,
  CHEAT_TAC);;

let try_update_twice = prove
 (`n < LENGTH ts ==>
   EL n (try_update ty idx1 (try_update ty idx2 ts)) =
     (match (idx1,idx2) with
       (NONE,NONE) -> EL n ts | (NONE,SOME b) ->
         (if ~(n = b) then EL n ts else if EL n ts = bvi_tailrec_Any
           then ty else EL n ts) | (SOME a,NONE) ->
         (if ~(n = a) then EL n ts else if EL n ts = bvi_tailrec_Any
           then ty else EL n ts) | (SOME a,SOME b) ->
         (if ~(n = a) /\ ~(n = b) then EL n ts else if EL n ts =
           bvi_tailrec_Any then ty else EL n ts))`,
  CHEAT_TAC);;

(* [simp] *)
let index_of_simp = prove
 (`index_of exp = SOME n <=> exp = Var n`,
  CHEAT_TAC);;

let scan_expr_ty_rel = prove
 (`!ts loc xs env ys s vs t.
     ty_rel env ts /\
     scan_expr ts loc xs = ys /\
     evaluate (xs,env,s) = (Rval vs,t) ==>
       EVERY (ty_rel env o FST) ys /\
       ty_rel vs (MAP (FST o SND) ys)`,
  CHEAT_TAC);;

let check_op_thm = prove
 (`check_op ts opr loc exp = SOME expr ==>
   (?x y.
     bvi_tailrec_is_rec loc x /\
     term_ok ts (op_type opr) y /\
     expr = Op (to_op opr) [y; x] /\
     (exp = Op (to_op opr) [x; y] \/ exp = Op (to_op opr) [y; x]))`,
  CHEAT_TAC);;

let rewrite_scan_expr = prove
 (`!loc next' op acc ts exp tt ty p exp2 r opr.
   rewrite loc next' op acc ts exp = (p,exp2) /\ ~(op =
     bvi_tailrec_Noop) /\
   scan_expr ts loc [exp] = [(tt,ty,r,opr)] ==>
     (match opr with
       SOME op1 -> op = op1 ==> p | NONE -> ~p)`,
  CHEAT_TAC);;

let scan_expr_op_type = prove
 (`!ts loc xs ys.
     scan_expr ts loc xs = ys ==>
     EVERY (\(tt,ty,r,opr).
       match opr with
         SOME op -> ~(ty = bvi_tailrec_Any) ==> op_type op = ty |
           NONE -> T) ys`,
  CHEAT_TAC);;

let optimized_code_def = cake_define
  `optimized_code loc arity exp n c op =
     (?exp_aux exp_opt.
         compile_exp loc n arity exp = SOME (exp_aux,exp_opt) /\
         check_exp loc arity exp = SOME op /\
         sptree_lookup loc c = SOME (arity,exp_aux) /\
         sptree_lookup n c = SOME (arity + 1,exp_opt))`;;

let code_rel_subspt = prove
 (`bvi_tailrecProof_code_rel c1 x1 /\ subspt x1 x2 ==>
  bvi_tailrecProof_code_rel c1 x2`,
  CHEAT_TAC);;

let compile_each_LENGTH = prove
 (`!n prog. LENGTH (SND (bvi_tailrec_compile_each n prog)) >= LENGTH
  prog`,
  CHEAT_TAC);;

let free_names_def = cake_define
  `bvi_tailrecProof_free_names n (name:num) <=> (!k. ~(n +
  bvl_to_bvi_namespaces * k = name))`;;
hol4_overload "free_names" "bvi_tailrecProof_free_names";;

(* [local] *)
let more_free_names = prove
 (`bvi_tailrecProof_free_names n name ==> bvi_tailrecProof_free_names
  (n + bvl_to_bvi_namespaces) name`,
  CHEAT_TAC);;

(* [local] *)
let is_free_name = prove
 (`bvi_tailrecProof_free_names n name ==> ~(n = name)`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_exp_next_addr = prove
 (cake_as_vars (fun () ->
    `compile_exp loc next args exp = NONE ==>
        compile_exp loc (next + bvl_to_bvi_namespaces) args exp =
          NONE`),
  CHEAT_TAC);;

let compile_each_untouched = prove
 (`!next' prog prog2 loc exp arity.
     bvi_tailrecProof_free_names next' loc /\
     sptree_lookup loc (fromAList prog) = SOME (arity,exp) /\
     check_exp loc arity exp = NONE /\
     compile_exp loc next' arity exp = NONE /\
     bvi_tailrec_compile_each next' prog = (next1,prog2) ==>
       sptree_lookup loc (fromAList prog2) = SOME (arity,exp)`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_free_names_SUCSUC = prove
 (`!xs.
      EVERY (bvi_tailrecProof_free_names n o FST) xs ==>
        EVERY (bvi_tailrecProof_free_names (n +
          bvl_to_bvi_namespaces) o FST) xs`,
  CHEAT_TAC);;

let compile_each_touched = prove
 (`!next' prog prog2 loc exp arity.
     ALL_DISTINCT (MAP FST prog) /\
     EVERY (bvi_tailrecProof_free_names next' o FST) prog /\
     bvi_tailrecProof_free_names next' loc /\
     sptree_lookup loc (fromAList prog) = SOME (arity,exp) /\
     check_exp loc arity exp = SOME op /\
     bvi_tailrec_compile_each next' prog = (next1,prog2) ==>
       (?k. !exp_aux exp_opt.
         compile_exp loc (next' + bvl_to_bvi_namespaces * k) arity
           exp = SOME (exp_aux,exp_opt) ==>
           sptree_lookup loc (fromAList prog2) = SOME (arity,exp_aux)
             /\
           sptree_lookup (next' + bvl_to_bvi_namespaces * k)
             (fromAList prog2) = SOME (arity + 1,exp_opt))`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let check_exp_NONE_compile_exp = prove
 (cake_as_vars (fun () ->
    `check_exp loc arity exp = NONE ==> compile_exp loc next arity exp
  = NONE`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let check_exp_SOME_compile_exp = prove
 (cake_as_vars (fun () ->
    `check_exp loc arity exp = SOME p ==>
        (?q. compile_exp loc next arity exp = SOME q)`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let EVERY_free_names_thm = prove
 (cake_as_vars (fun () ->
    `EVERY (bvi_tailrecProof_free_names next o FST) prog /\
      sptree_lookup loc (fromAList prog) = SOME x ==>
        bvi_tailrecProof_free_names next loc`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_each_code_rel = prove
 (cake_as_vars (fun () ->
    `bvi_tailrec_compile_each next prog = (next1,prog2) /\
     ALL_DISTINCT (MAP FST prog) /\
     EVERY (bvi_tailrecProof_free_names next o FST) prog ==>
       bvi_tailrecProof_code_rel (fromAList prog) (fromAList
         prog2)`),
  CHEAT_TAC);;

let compile_each_next_mono = prove
 (`!n xs n1 ys. bvi_tailrec_compile_each n xs = (n1,ys) ==> (?k. n1 =
  n + bvl_to_bvi_namespaces * k)`,
  CHEAT_TAC);;

let compile_prog_next_mono = prove
 (`!b n xs n1 ys. compile_prog b n xs = (n1,ys) ==> (?k. n1 = n +
  bvl_to_bvi_namespaces * k)`,
  CHEAT_TAC);;

let compile_each_MEM = prove
 (`bvi_tailrec_compile_each n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/ (n <= e /\ e < n1 /\ (?k. e = n + k *
     bvl_to_bvi_namespaces))`,
  CHEAT_TAC);;

let compile_prog_MEM = prove
 (`compile_prog b n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/ (n <= e /\ e < n1 /\ (?k. e = n + k *
     bvl_to_bvi_namespaces))`,
  CHEAT_TAC);;

(* [local] *)
let compile_each_intro = prove
 (`!xs n ys n1 name.
     ~(MEM name (MAP FST xs)) /\
     bvi_tailrecProof_free_names n name /\
     bvi_tailrec_compile_each n xs = (n1,ys) ==>
       ~(MEM name (MAP FST ys)) /\
       bvi_tailrecProof_free_names n1 name`,
  CHEAT_TAC);;

let compile_each_ALL_DISTINCT = prove
 (`bvi_tailrec_compile_each n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs)
  /\
   EVERY (bvi_tailrecProof_free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\
   EVERY (bvi_tailrecProof_free_names n1 o FST) ys`,
  CHEAT_TAC);;

let compile_prog_ALL_DISTINCT = prove
 (`compile_prog b n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   EVERY (bvi_tailrecProof_free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\
   EVERY (bvi_tailrecProof_free_names n1 o FST) ys`,
  CHEAT_TAC);;

let namespace_rel_def = cake_define
  `bvi_tailrecProof_namespace_rel (c1:'a spt) (c2:'a spt) <=>
     (!n. n IN domain c2 /\ bvl_num_stubs <= n ==> (if (\n. n MOD
       bvl_to_bvi_namespaces = 2) n then ~(n IN domain c1) else n IN
       domain c1)) /\
     (!n. n IN domain c1 /\ bvl_num_stubs <= n ==> ~((\n. n MOD
       bvl_to_bvi_namespaces = 2) n)) /\
     (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;
hol4_overload "namespace_rel" "bvi_tailrecProof_namespace_rel";;

let input_condition_def = cake_define
  `bvi_tailrecProof_input_condition next' prog <=>
     EVERY (bvi_tailrecProof_free_names next' o FST) prog /\
    ALL_DISTINCT (MAP FST prog) /\
    EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 2) o FST) (FILTER
      ((<=) bvl_num_stubs o FST) prog) /\
    bvl_num_stubs <= next' /\ (\n. n MOD bvl_to_bvi_namespaces =
      2) next'`;;
hol4_overload "input_condition" "bvi_tailrecProof_input_condition";;

let bvi_tailrecProof_state_rel_def = cake_define
  `bvi_tailrecProof_state_rel s (t:('a,'ffi)bviSem_state) <=>
  bviSem_state_refs
     t = state_refs s /\ bviSem_state_clock
     t = state_clock s /\ bviSem_state_global
     t = bviSem_state_global s /\ bviSem_state_ffi
     t = state_ffi s /\ bviSem_state_compile_oracle
     t = state_co bvi_tailrec_compile_each (compile_oracle s) /\
       compile
     s = state_cc bvi_tailrec_compile_each (bviSem_state_compile t)
       /\
     bvi_tailrecProof_code_rel (state_code s) (bviSem_state_code t)
       /\
     bvi_tailrecProof_namespace_rel (state_code s) (bviSem_state_code
       t) /\
     (!n. let ((next',cfg),prog) = compile_oracle s n in
             bvi_tailrecProof_input_condition next' prog) /\
     (!n. n IN domain (bviSem_state_code t) /\ (\n. n MOD
       bvl_to_bvi_namespaces = 2) n ==> n < FST (FST (compile_oracle
       s 0)))`;;
hol4_overload "state_rel" "bvi_tailrecProof_state_rel";;

let state_rel_const = prove
 (`bvi_tailrecProof_state_rel s t ==> state_refs
    t = state_refs s /\ state_clock
    t = state_clock s /\ bviSem_state_global
    t = bviSem_state_global s /\ state_ffi
    t = state_ffi s`,
  CHEAT_TAC);;

let state_rel_with_clock = prove
 (`bvi_tailrecProof_state_rel s t ==> bvi_tailrecProof_state_rel
  (state_clock_fupd (K k) s) (state_clock_fupd (K k) t)`,
  CHEAT_TAC);;

let state_rel_code_rel = prove
 (`bvi_tailrecProof_state_rel s t ==> bvi_tailrecProof_code_rel
  (state_code s) (state_code t)`,
  CHEAT_TAC);;

let code_rel_union = prove
 (`bvi_tailrecProof_code_rel x y /\ bvi_tailrecProof_code_rel t s /\
   // (∀a. a ∉ domain x ∧ a ∈ domain s ⇒ a ∉ domain y) ∧
   // (∀a. a ∉ domain x ∧ a ∈ domain y ⇒ a ∉ domain s)
   DISJOINT (domain s) (domain y) ==>
    // DISJOINT (domain s DIFF domain t) (domain y DIFF domain x)
    bvi_tailrecProof_code_rel (sptree_union x t) (sptree_union y s)`,
  CHEAT_TAC);;

let namespace_rel_union = prove
 (`bvi_tailrecProof_namespace_rel x y /\ bvi_tailrecProof_namespace_rel
  t s /\
   DISJOINT (domain s) (domain y) ==>
   bvi_tailrecProof_namespace_rel (sptree_union x t) (sptree_union
     y s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_each_namespace_rel = prove
 (cake_as_vars (fun () ->
    `bvi_tailrec_compile_each next prog = (next1,prog2) /\ (\n. n MOD
  bvl_to_bvi_namespaces = 2) next /\ bvl_num_stubs <= next /\
     EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 2) o FST)
       (FILTER ((<=) bvl_num_stubs o FST) prog) ==>
     bvi_tailrecProof_namespace_rel (fromAList prog) (fromAList
       prog2)`),
  CHEAT_TAC);;

let state_rel_do_app_aux = prove
 (`bviSem_do_app_aux op vs s = res /\
   bvi_tailrecProof_state_rel s t /\ ~(op = closLang_Install) /\ (!n.
     ~(op = closLang_Label n)) ==>
   (?res'.
     bviSem_do_app_aux op vs t = res' /\
     OPTREL (OPTREL (RPROD (=) bvi_tailrecProof_state_rel)) res
       res')`,
  CHEAT_TAC);;

let state_rel_do_app = prove
 (`bviSem_do_app op vs s = Rval (r,s') /\
   bvi_tailrecProof_state_rel s t /\ ~(op = closLang_Install) /\ (!n.
     ~(op = closLang_Label n)) ==>
   (?t'.
     bviSem_do_app op vs t = Rval (r,t') /\
     bvi_tailrecProof_state_rel s' t')`,
  CHEAT_TAC);;

let state_rel_do_app_err = prove
 (`bviSem_do_app op vs s = Rerr e /\
   bvi_tailrecProof_state_rel s t /\ ~(op = closLang_Install) /\ (!n.
     ~(op = closLang_Label n)) /\ (!n. ~(op = closLang_BlockOp
     (closLang_Build n))) ==>
   bviSem_do_app op vs t = Rerr e`,
  CHEAT_TAC);;

let do_app_to_op_state = prove
 (`bviSem_do_app (to_op op) vs s = Rval (r,t) ==> t = s`,
  CHEAT_TAC);;

let scan_expr_check_op = prove
 (`scan_expr ts loc [Op op xs] = [(tt,ty,r,SOME opr)] ==>
     IS_SOME (check_op ts opr loc (Op op xs))`,
  CHEAT_TAC);;

(* [simp] *)
let from_op_to_op = prove
 (`from_op (to_op opr) = opr`,
  CHEAT_TAC);;

let scan_expr_op_same = prove
 (`scan_expr ts loc [Op op xs] = [(tt,ty,r,SOME opr)] ==>
     op = to_op opr`,
  CHEAT_TAC);;

let term_ok_int_extend = prove
 (`!ts exp extra.
     term_ok_int ts exp ==> term_ok_int (ts ++ extra) exp`,
  CHEAT_TAC);;

let term_ok_any_extend = prove
 (`!ts list' exp extra.
     term_ok_any ts list' exp ==> term_ok_any (ts ++ extra) list'
       exp`,
  CHEAT_TAC);;

let term_ok_extend = prove
 (`!ts ty exp extra.
     term_ok ts ty exp ==> term_ok (ts ++ extra) ty exp`,
  CHEAT_TAC);;

let decide_ty_imp = prove
 (`~(decide_ty ty1 ty2 = bvi_tailrec_Any) ==> ~(ty1 = bvi_tailrec_Any)
  /\ ~(ty2 = bvi_tailrec_Any)`,
  CHEAT_TAC);;

let op_type_simp = prove
 (`(List = op_type op <=> op = Append) /\
   (bvi_tailrec_Any = op_type op <=> op = bvi_tailrec_Noop) /\
   (Int = op_type op <=> op = bvi_tailrec_Plus \/ op =
     bvi_tailrec_Times)`,
  CHEAT_TAC);;

let scan_expr_Op = prove
 (`scan_expr ts loc [Op op xs] = [(tt,ty,r,SOME opr)] /\
   rewrite loc n op1 acc ts (Op op xs) = (lr,x) ==>
     op = to_op opr /\
     (op1 = opr <=> lr)`,
  CHEAT_TAC);;

let is_rec_term_ok = prove
 (`!exp ts loc ty.
     (bvi_tailrec_is_rec loc exp ==> ~(term_ok ts ty exp)) /\
     (term_ok ts ty exp ==> ~(bvi_tailrec_is_rec loc exp))`,
  CHEAT_TAC);;

(* [simp] *)
let op_type_lem = prove
 (`~(op = bvi_tailrec_Noop) <=> ~(op_type op = bvi_tailrec_Any)`,
  CHEAT_TAC);;

let evaluate_rewrite_tail = prove
 (`!xs ((s:(num#'c,'ffi)bviSem_state)) env1 r t opt s' acc env2 loc ts
  ty.
     evaluate (xs,env1,s) = (r,t) /\
     bvi_tailrecProof_env_rel ty opt acc env1 env2 /\
     bvi_tailrecProof_state_rel s s' /\
     ty_rel env1 ts /\
     (opt ==> LENGTH xs = 1) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
       (?t'.
       evaluate (xs,env2,s') = (r,t') /\
       bvi_tailrecProof_state_rel t t' /\
       (opt ==>
         (!op n exp arity.
           sptree_lookup loc (bviSem_state_code s) = SOME (arity,exp)
             /\
           optimized_code loc arity exp n (state_code s') op /\
           op_type op = ty /\
           (?op1 tt ty r.
             scan_expr ts loc [HD xs] = [(tt,ty,r,SOME op1)] /\ ~(ty
               = bvi_tailrec_Any) /\ ~(op1 = bvi_tailrec_Noop) /\
               op_type op1 = op_type op) ==>
               (let (lr,x) = rewrite loc n op acc ts (HD xs) in
                 ?rrr t1 t2.
                 evaluate ([x],env2,s') = (rrr,t1) /\
                 evaluate ([apply_op op (Var acc) (HD xs)],
                   env2,s') = (rrr,t2) /\
                 bvi_tailrecProof_state_rel t t1 /\
                 bvi_tailrecProof_state_rel t t2))))`,
  CHEAT_TAC);;

(* HOL4 bvi_tailrecProofScript.sml:1349-1351: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:1353-1379: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:1381-1386: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:1388-1403: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:1405-1413: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:1415-1466: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:1468-1681: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:1683-1857: a proof *)
(* HOL4 bvi_tailrecProofScript.sml:1858: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1859: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1860: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1861-1868: a proof *)
(* HOL4 bvi_tailrecProofScript.sml:1869: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1870-2050: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:2052-2132: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:2134-2332: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:2334-2342: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:2344-2439: a proof *)

(* HOL4 bvi_tailrecProofScript.sml:2441: a proof *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let evaluate_compile_each = prove
 (cake_as_vars (fun () ->
    `bvi_tailrecProof_input_condition next' prog /\
     (!n next' cfg prog. co n = ((next',cfg),prog) ==>
       bvi_tailrecProof_input_condition next' prog) /\
     (!n. MEM n (MAP FST (SND (bvi_tailrec_compile_each next'
       prog))) /\ (\n. n MOD bvl_to_bvi_namespaces = 2) n ==> n < FST
       (FST (co 0))) /\
     evaluate ([Call 0 (SOME start) [] NONE],[],
               initial_state ffi0 (fromAList prog) co
                   (state_cc bvi_tailrec_compile_each cc) k) =
                     (r,s) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     (?s2.
       evaluate
        ([Call 0 (SOME start) [] NONE],[],
          initial_state ffi0 (fromAList (SND
            (bvi_tailrec_compile_each next' prog)))
              (state_co bvi_tailrec_compile_each co) cc k) = (r,s2)
                /\
       bvi_tailrecProof_state_rel s s2)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_each_semantics = prove
 (cake_as_vars (fun () ->
    `bvi_tailrecProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==>
       bvi_tailrecProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ (\n. n MOD bvl_to_bvi_namespaces
       = 2) k ==> k < FST (FST (co 0))) /\
     SND (bvi_tailrec_compile_each n prog) = prog2 /\ ~(semantics
       ffi (fromAList prog) co (state_cc bvi_tailrec_compile_each cc)
       start =
        ffi_Fail) ==>
     semantics ffi (fromAList prog) co (state_cc
       bvi_tailrec_compile_each cc) start =
     semantics ffi (fromAList prog2) (state_co
       bvi_tailrec_compile_each co) cc start`),
  CHEAT_TAC);;

(* compile_prog_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvi_tailrecProof_compile_prog_semantics = prove
 (cake_as_vars (fun () ->
    `bvi_tailrecProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==>
       bvi_tailrecProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ (\n. n MOD bvl_to_bvi_namespaces
       = 2) k ==> k < FST (FST (co 0))) /\
     SND (compile_prog b n prog) = prog2 /\ ~(semantics ffi
       (fromAList prog) co (state_cc (compile_prog b) cc) start =
        ffi_Fail) ==>
     semantics ffi (fromAList prog) co (state_cc (compile_prog b)
       cc) start =
     semantics ffi (fromAList prog2) (state_co (compile_prog b)
       co) cc start`),
  CHEAT_TAC);;

let compile_each_labels = prove
 (`!next1 code1 next2 code2.
     bvi_tailrec_compile_each next1 code1 = (next2,code2) ==>
     set_of_list (MAP FST code1) UNION {next1 + k *
       bvl_to_bvi_namespaces | k | next1 + k * bvl_to_bvi_namespaces <
       next2} =
     set_of_list (MAP FST code2) /\
     next1 <= next2`,
  CHEAT_TAC);;

let compile_each_keeps_names = prove
 (`!next' xs next' ys. bvi_tailrec_compile_each next' xs = (next',ys)
  /\ MEM x (MAP FST xs) ==> MEM x (MAP FST ys)`,
  CHEAT_TAC);;

let compile_prog_keeps_names = prove
 (`!b next' xs next' ys.
     compile_prog b next' xs = (next',ys) /\ MEM x (MAP FST xs) ==>
       MEM x (MAP FST ys)`,
  CHEAT_TAC);;

let get_code_labels_rewrite = prove
 (`!loc next' op arity foo exp bar exp_opt.
    rewrite loc next' op arity foo exp = (bar,exp_opt) ==>
    get_code_labels exp_opt SUBSET next' INSERT get_code_labels exp`,
  CHEAT_TAC);;

(* [simp] *)
let get_code_labels_let_wrap = prove
 (`!a b c. get_code_labels (let_wrap a b c) = get_code_labels b UNION
  get_code_labels c`,
  CHEAT_TAC);;

let get_code_labels_compile_exp = prove
 (`!loc next' arity exp exp_aux exp_opt.
   compile_exp loc next' arity exp = SOME (exp_aux,exp_opt) ==>
   get_code_labels exp_aux UNION get_code_labels exp_opt SUBSET
     next' INSERT get_code_labels exp`,
  CHEAT_TAC);;

let compile_each_good_code_labels = prove
 (`!n c n2 c2.
   bvi_tailrec_compile_each n c = (n2,c2) /\
   BIGUNION (set_of_list (MAP (bviProps_get_code_labels o SND o SND)
     c)) SUBSET all /\
   {n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces
     < n2} SUBSET all ==>
   BIGUNION (set_of_list (MAP (bviProps_get_code_labels o SND o
     SND) c2)) SUBSET all`,
  CHEAT_TAC);;

(* compile_prog_good_code_labels *)
let bvi_tailrecProof_compile_prog_good_code_labels = prove
 (`!b n c n2 c2.
   bvi_tailrec_compile_prog b n c = (n2,c2) /\
   BIGUNION (set_of_list (MAP (bviProps_get_code_labels o SND o SND)
     c)) SUBSET all /\
   {n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces
     < n2} SUBSET all ==>
   BIGUNION (set_of_list (MAP (bviProps_get_code_labels o SND o
     SND) c2)) SUBSET all`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["all"];;
