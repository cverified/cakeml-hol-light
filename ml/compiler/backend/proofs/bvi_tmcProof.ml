(* ======================================================== *)
(*  bvi_tmcProof: ported from HOL4's
    compiler/backend/proofs/bvi_tmcProofScript.sml
    A proof theory about bvi_tmc.ml, with 25 definitions and 169
    theorems.  Needed by bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_tailrec
*)

needs "basis/pure/mlvector.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tmc.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 bvi_tmcProofScript.sml:10: the ML values that the definitions
   below antiquote *)

(* HOL4 bvi_tmcProofScript.sml:12: the overload in_ns_3, which the
   port expands *)

let v_rel = cake_inductive
  `(!f i. bvi_tmcProof_v_rel f (bvlSem_Number i) (bvlSem_Number i)) /\
   (!f w. bvi_tmcProof_v_rel f (bvlSem_Word64 w) (bvlSem_Word64 w))
     /\
   (!f n xs ys.
       LIST_REL (bvi_tmcProof_v_rel f) xs ys ==>
       bvi_tmcProof_v_rel f (bvlSem_Block n xs) (bvlSem_Block n ys))
         /\
   (!f n. bvi_tmcProof_v_rel f (bvlSem_CodePtr n) (bvlSem_CodePtr n))
     /\
   (!f n m b.
       FLOOKUP f n = SOME m ==>
       bvi_tmcProof_v_rel f (bvlSem_RefPtr b n) (bvlSem_RefPtr b
         m))`;;
hol4_overload "v_rel" "bvi_tmcProof_v_rel";;

let ref_rel = cake_inductive
  `(bvi_tmcProof_ref_rel f (bvlSem_ByteArray b bs) (bvlSem_ByteArray b
  bs)) /\
   (LIST_REL (bvi_tmcProof_v_rel f) xs ys ==>
     bvi_tmcProof_ref_rel f (bvlSem_ValueArray xs) (bvlSem_ValueArray
       ys)) /\
   (bvi_tmcProof_v_rel f x y ==>
     bvi_tmcProof_ref_rel f (bvlSem_Thunk tm x) (bvlSem_Thunk tm
       y))`;;
hol4_overload "ref_rel" "bvi_tmcProof_ref_rel";;

let env_rel_def = cake_define
  `bvi_tmcProof_env_rel opt f env1 env2 <=>
   (?xs ys.
     env2 = xs ++ ys /\
     LIST_REL (bvi_tmcProof_v_rel f) env1 xs /\
     (opt ==>
       LENGTH ys = 2 /\
       (?hole_ptr hole_idx.
         EL 0 ys = RefPtr F hole_ptr /\
         EL 1 ys = Number hole_idx /\
         small_enough_int hole_idx)))`;;
hol4_overload "env_rel" "bvi_tmcProof_env_rel";;

let no_mutcons_op_def = cake_define
  `no_mutcons_op op <=> (!tag i. ~(op = closLang_MemOp
  (closLang_MutCons tag i)))`;;

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let no_mutcons_def = cake_define_list_try (fun () ->
  `MEASURE flatLang_exp_size`)
  [`no_mutcons (Var n:bvi_exp) <=> T`;
   `no_mutcons (If x1 x2 x3:bvi_exp) <=> no_mutcons x1 /\ no_mutcons
  x2 /\ no_mutcons x3`;
   `no_mutcons (Let xs x:bvi_exp) <=> EVERY no_mutcons xs /\
  no_mutcons x`;
   `no_mutcons (Raise x:bvi_exp) <=> no_mutcons x`;
   `no_mutcons (Tick x:bvi_exp) <=> no_mutcons x`;
   `no_mutcons (Call ticks dest xs handler:bvi_exp) <=>
         EVERY no_mutcons xs /\ (match handler with NONE -> T |
           SOME x -> no_mutcons x)`;
   `no_mutcons (Force loc n:bvi_exp) <=> T`;
   `no_mutcons (bvi_LetCall rets ticks dest xs y) <=> EVERY
  no_mutcons xs /\ no_mutcons y`;
   `no_mutcons (bvi_Return xs:bvi_exp) <=> EVERY no_mutcons xs`;
   `no_mutcons (Op op xs:bvi_exp) <=> no_mutcons_op op /\ EVERY
  no_mutcons xs`];;

let code_rel_def = cake_define
  `bvi_tmcProof_code_rel c1 c2 <=>
     (!loc arity exp.
       sptree_lookup loc c1 = SOME (arity,exp) ==>
       no_mutcons exp /\
       (?n.
         (compile_exp loc n arity exp = NONE ==>
          sptree_lookup loc c2 = SOME (arity,exp)) /\
         (!wrap work.
           compile_exp loc n arity exp = SOME (wrap,work) ==>
           sptree_lookup loc c2 = SOME (arity,wrap) /\
           sptree_lookup n c2 = SOME (arity + 2,work))))`;;
hol4_overload "code_rel" "bvi_tmcProof_code_rel";;

let bvi_tmcProof_code_rel_domain = cake_theorem "code_rel_domain"
  (fun () ->
    `!c1 c2.
       bvi_tmcProof_code_rel c1 c2 ==> domain c1 SUBSET domain c2`)
  CHEAT_TAC;;

let free_names_def = cake_define
  `bvi_tmcProof_free_names n (name:num) <=> (!k. ~(n +
  bvl_to_bvi_namespaces * k = name))`;;
hol4_overload "free_names" "bvi_tmcProof_free_names";;

let namespace_rel_def = cake_define
  `bvi_tmcProof_namespace_rel (c1:'a spt) (c2:'a spt) <=>
     (!n. n IN domain c2 /\ bvl_num_stubs <= n ==> (if (\n. n MOD
       bvl_to_bvi_namespaces = 3) n then ~(n IN domain c1) else n IN
       domain c1)) /\
     (!n. n IN domain c1 /\ bvl_num_stubs <= n ==> ~((\n. n MOD
       bvl_to_bvi_namespaces = 3) n)) /\
     (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;
hol4_overload "namespace_rel" "bvi_tmcProof_namespace_rel";;

(* This should say: expression in prog satisfies no-mutblock property *)
let input_condition_def = cake_define
  `bvi_tmcProof_input_condition next' prog <=>
     EVERY (bvi_tmcProof_free_names next' o FST) prog /\
     EVERY (no_mutcons o SND o SND) prog /\
     ALL_DISTINCT (MAP FST prog) /\
     EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 3) o FST)
       (FILTER ((<=) bvl_num_stubs o FST) prog) /\
     bvl_num_stubs <= next' /\ (\n. n MOD bvl_to_bvi_namespaces =
       3) next'`;;
hol4_overload "input_condition" "bvi_tmcProof_input_condition";;

let state_ref_rel_def = cake_define
  `state_ref_rel f (s_refs:(num,bvlSem_v bvlSem_ref)fmap)
  (t_refs:(num,bvlSem_v bvlSem_ref)fmap) <=>
     FDOM f = FDOM s_refs /\
     (!i v.
       FLOOKUP s_refs i = SOME v ==>
        (?j w. FLOOKUP f i = SOME j /\
              bvi_tmcProof_ref_rel f v w /\
              FLOOKUP t_refs j = SOME w))`;;

let fmap_inj_def = cake_define
  `fmap_inj (f:(num,num)fmap) <=>
     (!p1 p2 q. FLOOKUP f p1 = SOME q /\ FLOOKUP f p2 = SOME q ==>
       p1 = p2)`;;

let fmap_inj_FEMPTY = cake_theorem "fmap_inj_FEMPTY[simp]"
  (fun () ->
    `fmap_inj FEMPTY`)
  CHEAT_TAC;;

let fmap_inj_update = cake_theorem "fmap_inj_update"
  (fun () ->
    `!f k v.
       fmap_inj f /\ ~(v IN FRANGE f) ==>
       fmap_inj (f |+ (k,v))`)
  CHEAT_TAC;;

let state_rel_def = cake_define
  `bvi_tmcProof_state_rel f s (t:('a,'ffi)bviSem_state) <=>
     state_ref_rel f (state_refs s) (state_refs t) /\ state_clock
     t = state_clock s /\
     OPTREL (\p p'. FLOOKUP f p = SOME p') (bviSem_state_global s)
       (bviSem_state_global t) /\ state_ffi
     t = state_ffi s /\ compile_oracle
     t = state_co bvi_tmc_compile_each (compile_oracle s) /\ compile
     s = state_cc bvi_tmc_compile_each (compile t) /\
     bvi_tmcProof_code_rel (state_code s) (state_code t) /\
     bvi_tmcProof_namespace_rel (state_code s) (state_code t) /\
     (!n. let ((next',cfg),prog) = compile_oracle s n in
             bvi_tmcProof_input_condition next' prog) /\
     (!n. n IN domain (state_code t) /\ (\n. n MOD
       bvl_to_bvi_namespaces = 3) n ==> n < FST (FST (compile_oracle s
       0))) /\
     fmap_inj f`;;
hol4_overload "state_rel" "bvi_tmcProof_state_rel";;

(* Structural facts about compile_each and the namespace allocation.
   These follow bvi_tailrecProof; they only depend on the recursion shape of
   compile_each (NONE keeps an entry, SOME emits wrapper + worker). *)

let bvi_tmcProof_more_free_names = cake_theorem "more_free_names[local]"
  (fun () ->
    `bvi_tmcProof_free_names n name ==> bvi_tmcProof_free_names (n +
  bvl_to_bvi_namespaces) name`)
  CHEAT_TAC;;

let bvi_tmcProof_is_free_name = cake_theorem "is_free_name[local]"
  (fun () ->
    `bvi_tmcProof_free_names n name ==> ~(n = name)`)
  CHEAT_TAC;;

let bvi_tmcProof_EVERY_free_names_SUCSUC =
  cake_theorem "EVERY_free_names_SUCSUC[local]"
  (fun () ->
    `!xs. EVERY (bvi_tmcProof_free_names n o FST) xs ==>
          EVERY (bvi_tmcProof_free_names (n +
            bvl_to_bvi_namespaces) o FST) xs`)
  CHEAT_TAC;;

let bvi_tmcProof_EVERY_free_names_thm =
  cake_theorem "EVERY_free_names_thm[local]"
  (fun () ->
    `EVERY (bvi_tmcProof_free_names next o FST) prog /\ sptree_lookup
  loc (fromAList prog) = SOME x ==>
     bvi_tmcProof_free_names next loc`)
  CHEAT_TAC;;

let free_names_mult_F = cake_theorem "free_names_mult_F[local,simp]"
  (fun () ->
    `bvi_tmcProof_free_names n (n + k * bvl_to_bvi_namespaces') <=> F`)
  CHEAT_TAC;;

let free_names_refl_F = cake_theorem "free_names_refl_F[local,simp]"
  (fun () ->
    `bvi_tmcProof_free_names n n <=> F`)
  CHEAT_TAC;;

let free_names_succ_F = cake_theorem "free_names_succ_F[local,simp]"
  (fun () ->
    `bvi_tmcProof_free_names n (n + (bvl_to_bvi_namespaces' + k *
  bvl_to_bvi_namespaces')) <=> F`)
  CHEAT_TAC;;

let rewrite_wrapper_NONE_irrel =
  cake_theorem "rewrite_wrapper_NONE_irrel[local]"
  (fun () ->
    `!loc lo1 n exp lo2.
       rewrite_wrapper loc lo1 n exp = NONE ==> rewrite_wrapper
         loc lo2 n exp = NONE`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_exp_next_addr =
  cake_theorem "compile_exp_next_addr[local]"
  (fun () ->
    `compile_exp loc next args exp = NONE ==>
     compile_exp loc (next + bvl_to_bvi_namespaces) args exp =
       NONE`)
  CHEAT_TAC;;

let compile_exp_SOME_irrel =
  cake_theorem "compile_exp_SOME_irrel[local]"
  (fun () ->
    `compile_exp loc next args exp = SOME w ==>
     (?w'. compile_exp loc next2 args exp = SOME w')`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_LENGTH =
  cake_theorem "compile_each_LENGTH"
  (fun () ->
    `!n prog. LENGTH (SND (bvi_tmc_compile_each n prog)) >= LENGTH
  prog`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_next_mono =
  cake_theorem "compile_each_next_mono"
  (fun () ->
    `!n xs n1 ys. bvi_tmc_compile_each n xs = (n1,ys) ==> (?k. n1 = n
  + bvl_to_bvi_namespaces * k)`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_prog_next_mono =
  cake_theorem "compile_prog_next_mono"
  (fun () ->
    `!b n xs n1 ys. compile_prog b n xs = (n1,ys) ==> (?k. n1 = n +
  bvl_to_bvi_namespaces * k)`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_MEM = cake_theorem "compile_each_MEM"
  (fun () ->
    `bvi_tmc_compile_each n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
     MEM e (MAP FST xs) \/ (n <= e /\ e < n1 /\ (?k. e = n + k *
       bvl_to_bvi_namespaces))`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_prog_MEM = cake_theorem "compile_prog_MEM"
  (fun () ->
    `compile_prog b n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
     MEM e (MAP FST xs) \/ (n <= e /\ e < n1 /\ (?k. e = n + k *
       bvl_to_bvi_namespaces))`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_intro =
  cake_theorem "compile_each_intro[local]"
  (fun () ->
    `!xs n ys n1 name.
       ~MEM name (MAP FST xs) /\ bvi_tmcProof_free_names n name /\
       bvi_tmc_compile_each n xs = (n1,ys) ==>
         ~MEM name (MAP FST ys) /\ bvi_tmcProof_free_names n1
           name`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_ALL_DISTINCT =
  cake_theorem "compile_each_ALL_DISTINCT"
  (fun () ->
    `bvi_tmc_compile_each n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
     EVERY (bvi_tmcProof_free_names n o FST) xs ==>
     ALL_DISTINCT (MAP FST ys) /\ EVERY (bvi_tmcProof_free_names
       n1 o FST) ys`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_prog_ALL_DISTINCT =
  cake_theorem "compile_prog_ALL_DISTINCT"
  (fun () ->
    `compile_prog b n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
     EVERY (bvi_tmcProof_free_names n o FST) xs ==>
     ALL_DISTINCT (MAP FST ys) /\ EVERY (bvi_tmcProof_free_names
       n1 o FST) ys`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_namespace_rel =
  cake_theorem "compile_each_namespace_rel"
  (fun () ->
    `bvi_tmc_compile_each next prog = (next1,prog2) /\ (\n. n MOD
  bvl_to_bvi_namespaces = 3) next /\ bvl_num_stubs <= next /\
     EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 3) o FST)
       (FILTER ((<=) bvl_num_stubs o FST) prog) ==>
     bvi_tmcProof_namespace_rel (fromAList prog) (fromAList
       prog2)`)
  CHEAT_TAC;;

let bvi_tmcProof_namespace_rel_union =
  cake_theorem "namespace_rel_union"
  (fun () ->
    `bvi_tmcProof_namespace_rel x y /\ bvi_tmcProof_namespace_rel t s /\
  DISJOINT (domain s) (domain y) ==>
     bvi_tmcProof_namespace_rel (sptree_union x t) (sptree_union
       y s)`)
  CHEAT_TAC;;

let bvi_tmcProof_code_rel_union = cake_theorem "code_rel_union"
  (fun () ->
    `bvi_tmcProof_code_rel x y /\ bvi_tmcProof_code_rel t s /\ DISJOINT
  (domain s) (domain y) ==>
     bvi_tmcProof_code_rel (sptree_union x t) (sptree_union y s)`)
  CHEAT_TAC;;

let bvi_tmcProof_state_rel_code_rel = cake_theorem "state_rel_code_rel"
  (fun () ->
    `bvi_tmcProof_state_rel f s t ==> bvi_tmcProof_code_rel
  (state_code s) (state_code t)`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_untouched =
  cake_theorem "compile_each_untouched[local]"
  (fun () ->
    `!next' prog prog2 loc exp arity.
       bvi_tmcProof_free_names next' loc /\ sptree_lookup loc
         (fromAList prog) = SOME (arity,exp) /\
       compile_exp loc next' arity exp = NONE /\
       bvi_tmc_compile_each next' prog = (next1,prog2) ==>
         sptree_lookup loc (fromAList prog2) = SOME (arity,exp)`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_touched =
  cake_theorem "compile_each_touched[local]"
  (fun () ->
    `!next' prog prog2 loc exp arity.
       ALL_DISTINCT (MAP FST prog) /\ EVERY
         (bvi_tmcProof_free_names next' o FST) prog /\
       bvi_tmcProof_free_names next' loc /\ sptree_lookup loc
         (fromAList prog) = SOME (arity,exp) /\
       (?w. compile_exp loc next' arity exp = SOME w) /\
       bvi_tmc_compile_each next' prog = (next1,prog2) ==>
         (?k. !wrap work.
           compile_exp loc (next' + bvl_to_bvi_namespaces * k)
             arity exp = SOME (wrap,work) ==>
             sptree_lookup loc (fromAList prog2) = SOME
               (arity,wrap) /\
             sptree_lookup (next' + bvl_to_bvi_namespaces * k)
               (fromAList prog2) = SOME (arity + 2,work))`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_code_rel =
  cake_theorem "compile_each_code_rel"
  (fun () ->
    `bvi_tmc_compile_each next prog = (next1,prog2) /\ ALL_DISTINCT (MAP
  FST prog) /\
     EVERY (bvi_tmcProof_free_names next o FST) prog /\ EVERY
       (no_mutcons o SND o SND) prog ==>
     bvi_tmcProof_code_rel (fromAList prog) (fromAList prog2)`)
  CHEAT_TAC;;

let eor_rel_def = cake_define
  `eor_rel f x2 x3 =
        match (x2,x3) with
          (Exn v1,Exn v2) -> bvi_tmcProof_v_rel f v1 v2
        | ((Ret vs1),(Ret vs2)) -> LIST_REL (bvi_tmcProof_v_rel f)
          vs1 vs2
        | (_1,_2) -> F`;;

let opt_res_rel_def = cake_define
  `opt_res_rel f (r1:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result) (r2:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result) =
   (match (r1,r2) with (Rval v1,Rval [Block 0 []]) -> T | (Rerr
     e1,Rerr e2) -> exc_rel (eor_rel f) e1 e2 | _3 -> F)`;;

let v_rel_submap = cake_theorem "v_rel_submap"
  (fun () ->
    `!f v1 v2 f'. bvi_tmcProof_v_rel f v1 v2 /\ f SUBMAP f' ==>
  bvi_tmcProof_v_rel f' v1 v2`)
  CHEAT_TAC;;

let list_rel_submap = cake_theorem "list_rel_submap"
  (fun () ->
    `LIST_REL (bvi_tmcProof_v_rel f) env1 env2 /\ f SUBMAP f' ==>
  LIST_REL (bvi_tmcProof_v_rel f') env1 env2`)
  CHEAT_TAC;;

let env_rel_submap = cake_theorem "env_rel_submap"
  (fun () ->
    `bvi_tmcProof_env_rel opt f env1 env2 /\ f SUBMAP f' ==>
  bvi_tmcProof_env_rel opt f' env1 env2`)
  CHEAT_TAC;;

let env_rel_relax_opt = cake_theorem "env_rel_relax_opt"
  (fun () ->
    `!opt f env1 env2.
       bvi_tmcProof_env_rel opt f env1 env2 ==>
       bvi_tmcProof_env_rel F f env1 env2`)
  CHEAT_TAC;;

let env_rel_cons = cake_theorem "env_rel_cons"
  (fun () ->
    `bvi_tmcProof_env_rel opt f env1 env2 /\
     bvi_tmcProof_v_rel f a b ==>
     bvi_tmcProof_env_rel opt f (a :: env1) (b :: env2)`)
  CHEAT_TAC;;

let env_rel_append = cake_theorem "env_rel_append"
  (fun () ->
    `bvi_tmcProof_env_rel opt f env1 env2 /\
     LIST_REL (bvi_tmcProof_v_rel f) a b ==>
     bvi_tmcProof_env_rel opt f (a ++ env1) (b ++ env2)`)
  CHEAT_TAC;;

let env_rel_length_opt = cake_theorem "env_rel_length_opt"
  (fun () ->
    `!f env1 env2.
       bvi_tmcProof_env_rel T f env1 env2 ==>
       LENGTH env2 = LENGTH env1 + 2`)
  CHEAT_TAC;;

(* not a strict equality anymore! *)
let env_rel_length_non_opt = cake_theorem "env_rel_length_non_opt"
  (fun () ->
    `!f env1 env2.
       bvi_tmcProof_env_rel F f env1 env2 ==>
       LENGTH env2 >= LENGTH env1`)
  CHEAT_TAC;;

let bvi_tmcProof_env_rel_length = cake_theorem "env_rel_length"
  (fun () ->
    `!opt f env1 env2.
       bvi_tmcProof_env_rel opt f env1 env2 ==>
       LENGTH env2 >= LENGTH env1`)
  CHEAT_TAC;;

let env_rel_extras_opt = cake_theorem "env_rel_extras_opt"
  (fun () ->
    `!f env env'.
       bvi_tmcProof_env_rel T f env env' ==>
       (?hole_ptr hole_idx. EL (LENGTH env)
         env' = RefPtr F hole_ptr /\ EL (LENGTH env + 1)
         env' = Number hole_idx)`)
  CHEAT_TAC;;

let env_rel_el_v_rel = cake_theorem "env_rel_el_v_rel"
  (fun () ->
    `!opt f env1 env2 n.
       bvi_tmcProof_env_rel opt f env1 env2 /\
       n < LENGTH env1 ==>
       bvi_tmcProof_v_rel f (EL n env1) (EL n env2)`)
  CHEAT_TAC;;

let env_rel_strip_extras = cake_theorem "env_rel_strip_extras"
  (fun () ->
    `!f env1 env2.
       bvi_tmcProof_env_rel T f env1 env2 ==>
       (?env2' hole_ptr hole_idx.
         bvi_tmcProof_env_rel F f env1 env2' /\
         env2 = env2' ++ [RefPtr F hole_ptr; Number hole_idx] /\
         small_enough_int hole_idx)`)
  CHEAT_TAC;;

let state_rel_dec = cake_theorem "state_rel_dec"
  (fun () ->
    `!n t f s s'.
       bvi_tmcProof_state_rel f s s' /\ state_clock
       s = SUC n /\ state_clock
       s' = SUC n /\
       SUC n >= t ==>
       bvi_tmcProof_state_rel f (dec_clock t s) (dec_clock t s')`)
  CHEAT_TAC;;

let bvi_tmcProof_state_rel_with_clock =
  cake_theorem "state_rel_with_clock"
  (fun () ->
    `!n f s s'.
       bvi_tmcProof_state_rel f s s' ==>
       bvi_tmcProof_state_rel f (state_clock_fupd (K n) s)
         (state_clock_fupd (K n) s')`)
  CHEAT_TAC;;

let state_ref_rel_filled = cake_theorem "state_ref_rel_filled"
  (fun () ->
    `!f refs refs' k v.
       state_ref_rel f refs refs' /\ ~(
       k IN FRANGE f) ==>
       state_ref_rel f refs refs' |+ (k,v)`)
  CHEAT_TAC;;

let state_rel_filled = cake_theorem "state_rel_filled"
  (fun () ->
    `!f s s' k v.
       bvi_tmcProof_state_rel f s s' /\ ~(
       k IN FRANGE f) ==>
       bvi_tmcProof_state_rel f s (state_refs_fupd (K (state_refs
         s' |+ (k,v))) s')`)
  CHEAT_TAC;;

let hole_has_val_def = cake_define
  `hole_has_val (f:(num,num)fmap) (env1:bvlSem_v list) (env2:bvlSem_v
  list) (refs:(num,bvlSem_v bvlSem_ref)fmap) c <=>
   LENGTH env2 = LENGTH env1 + 2 /\
   (?hole_ptr tag finalised left right. EL (LENGTH env1)
     env2 = RefPtr F hole_ptr /\ EL (LENGTH env1 + 1)
     env2 = Number (&(LENGTH left)) /\
     small_enough_int (&(LENGTH left)) /\ ~(
     hole_ptr IN FRANGE f) /\
     FLOOKUP refs hole_ptr = SOME (bvlSem_MutBlock tag finalised
       left c right))`;;

let holes_unchanged_except_def = cake_define
  `holes_unchanged_except f refs refs' changed <=>
     (!ptr tag finalised left child right. ~(
        ptr IN FRANGE f) /\
        FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag finalised left
          child right) ==>
        (?finalised' child'.
          FLOOKUP refs' ptr = SOME (bvlSem_MutBlock tag finalised'
            left child' right) /\
          (~(ptr IN changed) ==> child = child')))`;;

let hole_not_finalised_def = cake_define
  `hole_not_finalised refs ptr <=>
     (?tag left child right.
       FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag F left child
         right))`;;

let holes_still_not_finalised_def = cake_define
  `holes_still_not_finalised f (refs:('b,'c bvlSem_ref)fmap)
  (refs':('b,'c bvlSem_ref)fmap) <=>
     (!ptr. ~(
       ptr IN FRANGE f) /\
       hole_not_finalised refs ptr ==>
       hole_not_finalised refs' ptr)`;;

let holes_still_not_finalised_refl =
  cake_theorem "holes_still_not_finalised_refl"
  (fun () ->
    `!f refs.
       holes_still_not_finalised f refs refs`)
  CHEAT_TAC;;

let holes_still_not_finalised_ins =
  cake_theorem "holes_still_not_finalised_ins"
  (fun () ->
    `!f refs refs' ptr tag l c r.
       holes_still_not_finalised f refs refs' ==>
       holes_still_not_finalised f refs refs' |+
         (ptr,bvlSem_MutBlock tag F l c r)`)
  CHEAT_TAC;;

let holes_still_not_finalised_del =
  cake_theorem "holes_still_not_finalised_del"
  (fun () ->
    `(!f refs refs' ptr tag l c r.
       holes_still_not_finalised f refs |+ (ptr,bvlSem_MutBlock tag
         F l c r)) refs' ==>
       holes_still_not_finalised f refs refs'`)
  CHEAT_TAC;;

let only_fresh_def = cake_define
  `only_fresh (f:(num,num)fmap) (f':(num,num)fmap)
  (refs_old:(num,bvlSem_v bvlSem_ref)fmap) =
   (!n. n IN FRANGE f' /\ ~(n IN FRANGE f) ==> ~(n IN FDOM
     refs_old))`;;

let holes_unchanged_except_refl =
  cake_theorem "holes_unchanged_except_refl"
  (fun () ->
    `!f refs changed. holes_unchanged_except f refs refs changed`)
  CHEAT_TAC;;

let holes_unchanged_except_submap =
  cake_theorem "holes_unchanged_except_submap"
  (fun () ->
    `!f f' refs refs' changed.
       holes_unchanged_except f refs refs' changed /\
       f SUBMAP f' ==>
       holes_unchanged_except f' refs refs' changed`)
  CHEAT_TAC;;

let holes_unchanged_except_trans =
  cake_theorem "holes_unchanged_except_trans"
  (fun () ->
    `!f f' refs refs' refs'' changed.
       holes_unchanged_except f refs refs' changed /\
       holes_unchanged_except f' refs' refs'' changed /\
       only_fresh f f' refs /\
       f SUBMAP f' ==>
       holes_unchanged_except f refs refs'' changed`)
  CHEAT_TAC;;

let holes_still_not_finalised_trans =
  cake_theorem "holes_still_not_finalised_trans"
  (fun () ->
    `!f f' refs refs' refs'' changed.
       holes_still_not_finalised f refs refs' /\
       holes_still_not_finalised f' refs' refs'' /\
       only_fresh f f' refs /\
       f SUBMAP f' ==>
       holes_still_not_finalised f refs refs''`)
  CHEAT_TAC;;

let holes_unchanged_except_subset =
  cake_theorem "holes_unchanged_except_subset"
  (fun () ->
    `!f refs refs' changed changed'.
       holes_unchanged_except f refs refs' changed /\
       changed SUBSET changed' ==>
       holes_unchanged_except f refs refs' changed'`)
  CHEAT_TAC;;

let holes_unchanged_except_del =
  cake_theorem "holes_unchanged_except_del"
  (fun () ->
    `(!f refs_old refs_new changed ptr v.
       holes_unchanged_except f refs_old |+ (ptr,v)) refs_new
         changed /\ ~(
       ptr IN FDOM refs_old) ==>
       holes_unchanged_except f refs_old refs_new (changed DIFF
         {ptr})`)
  CHEAT_TAC;;

let holes_unchanged_except_del_SING =
  cake_theorem "holes_unchanged_except_del_SING"
  (fun () ->
    `(!f refs_old refs_new changed ptr v.
       holes_unchanged_except f refs_old |+ (ptr,v)) refs_new {ptr}
         /\ ~(
       ptr IN FDOM refs_old) ==>
       holes_unchanged_except f refs_old refs_new EMPTY`)
  CHEAT_TAC;;

let holes_unchanged_except_changed =
  cake_theorem "holes_unchanged_except_changed"
  (fun () ->
    `(!f refs_old refs_new changed ptr tag fin l c r.
       holes_unchanged_except f refs_old |+ (ptr,bvlSem_MutBlock
         tag fin l c r)) refs_new EMPTY /\
       FLOOKUP refs_old ptr = SOME (bvlSem_MutBlock tag fin' l c'
         r) ==>
       holes_unchanged_except f refs_old refs_new {ptr}`)
  CHEAT_TAC;;

let holes_unchanged_except_filled =
  cake_theorem "holes_unchanged_except_filled"
  (fun () ->
    `(!f refs_old refs_new changed ptr tag fin l c r.
       holes_unchanged_except f refs_old refs_new EMPTY /\
       FLOOKUP refs_old ptr = SOME (bvlSem_MutBlock tag fin' l c'
         r) ==>
       holes_unchanged_except f refs_old refs_new |+
         (ptr,bvlSem_MutBlock tag fin l c r)) {ptr}`)
  CHEAT_TAC;;

let unchanged_hole_has_val = cake_theorem "unchanged_hole_has_val"
  (fun () ->
    `!f f' env env' hole_ptr hole_idx refs refs' c changed.
       hole_has_val f env (env' ++ [RefPtr F hole_ptr; Number
         hole_idx]) refs c /\
       only_fresh f f' refs /\
       holes_unchanged_except f refs refs' changed /\ ~(
       hole_ptr IN changed) ==>
       hole_has_val f' env (env' ++ [RefPtr F hole_ptr; Number
         hole_idx]) refs' c`)
  CHEAT_TAC;;

let hole_has_val_submap = cake_theorem "hole_has_val_submap"
  (fun () ->
    `!f f' env1 env2 refs c.
       hole_has_val f' env1 env2 refs c /\
       f SUBMAP f' ==>
       hole_has_val f env1 env2 refs c`)
  CHEAT_TAC;;

let hole_has_val_append = cake_theorem "hole_has_val_append"
  (fun () ->
    `!f env env' refs c vs vs'.
       hole_has_val f env env' refs c /\
       LIST_REL (bvi_tmcProof_v_rel f) vs vs' ==>
       hole_has_val f (vs ++ env) (vs' ++ env') refs c`)
  CHEAT_TAC;;

let hole_has_val_unappend = cake_theorem "hole_has_val_unappend"
  (fun () ->
    `!f.
       hole_has_val f (vs ++ env) (vs' ++ env') refs c /\
       LIST_REL (bvi_tmcProof_v_rel f) vs vs' ==>
       hole_has_val f env env' refs c`)
  CHEAT_TAC;;

let hole_has_val_dec = cake_theorem "hole_has_val_dec"
  (fun () ->
    `!f env env' s c n.
       hole_has_val f env env' (state_refs s) c /\ state_clock
       s = SUC n ==>
       hole_has_val f env env' (state_refs (dec_clock 1 s)) c`)
  CHEAT_TAC;;

let only_fresh_refl = cake_theorem "only_fresh_refl"
  (fun () ->
    `!f refs. only_fresh f f refs`)
  CHEAT_TAC;;

let only_fresh_trans = cake_theorem "only_fresh_trans"
  (fun () ->
    `!f f' f'' refs refs'.
       only_fresh f f' refs /\
       only_fresh f' f'' refs' /\
       FDOM refs SUBSET FDOM refs' ==>
       only_fresh f f'' refs`)
  CHEAT_TAC;;

let only_fresh_submap = cake_theorem "only_fresh_submap"
  (fun () ->
    `!f f' f'' refs.
       only_fresh f f'' refs /\
       f' SUBMAP f'' ==>
       only_fresh f f' refs`)
  CHEAT_TAC;;

let non_fresh_not_in_frange = cake_theorem "non_fresh_not_in_frange"
  (fun () ->
    `ptr IN FDOM refs_old /\ ~(
     ptr IN FRANGE f) /\
     only_fresh f f' refs_old ==> ~(
     ptr IN FRANGE f')`)
  CHEAT_TAC;;

let fresh_ptr_fresh = cake_theorem "fresh_ptr_fresh"
  (fun () ->
    `!refs. ~(
       (LEAST (\ptr. ~(ptr IN FDOM refs))) IN FDOM refs)`)
  CHEAT_TAC;;

let fresh_not_in_range_f = cake_theorem "fresh_not_in_range_f"
  (fun () ->
    `!f s_refs t_refs.
       state_ref_rel f s_refs t_refs ==> ~(
       (LEAST (\ptr. ~(ptr IN FDOM t_refs))) IN FRANGE f)`)
  CHEAT_TAC;;

let only_fresh_del = cake_theorem "only_fresh_del"
  (fun () ->
    `!f f' refs ptr v.
       only_fresh f f' refs |+ (ptr,v) /\ ~(
       ptr IN FRANGE f) ==>
       only_fresh f f' refs`)
  CHEAT_TAC;;

let flookup_com_neq = cake_theorem "flookup_com_neq"
  (fun () ->
    `!m k1 v1 k2 v2. ~(
       k1 = k2) ==>
       m |+ (k1,v1) |+ (k2,v2) = m |+ (k2,v2) |+ (k1,v1)`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:1095-1103: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let mb_rel_def = cake_define_try_tac (fun () ->
  `MEASURE (CARD o FDOM o FST o SND o SND)`)
  CHEAT_TAC
  `mb_rel f x2 refs v1 v2 =
        match (x2,v1,v2) with
          ((refs_old:(num,bvlSem_v bvlSem_ref)fmap),(Block tag
            xs:bvlSem_v),(RefPtr b ptr:bvlSem_v)) ->
      (if b \/ ptr IN FRANGE f \/ ptr IN FDOM refs_old then F else
        match FLOOKUP refs ptr with SOME (bvlSem_MutBlock tag' fin'
          left' child' right') ->
            (tag = tag' /\
             fin' = F /\
             (?left child right.
               xs = left ++ [child] ++ right /\
               LIST_REL (bvi_tmcProof_v_rel f) left left' /\
               mb_rel f refs_old (refs \\ ptr) child child' /\
               LIST_REL (bvi_tmcProof_v_rel f) right right')) | _4 ->
                 F)
        | (_5,v1,v2) -> bvi_tmcProof_v_rel f v1 v2`;;

let mb_rel_cons = cake_theorem "mb_rel_cons"
  (fun () ->
    `!refs_old refs ptr f tag left left' v v' right right'.
       mb_rel f refs_old (refs \\ ptr) v v' /\
       LIST_REL (bvi_tmcProof_v_rel f) left left' /\
       LIST_REL (bvi_tmcProof_v_rel f) right right' /\
       FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag F left' v'
         right') /\ ~(
       ptr IN FRANGE f) /\ ~(
       ptr IN FDOM refs_old) ==>
       mb_rel f refs_old refs (Block tag (left ++ [v] ++ right))
         (RefPtr F ptr)`)
  CHEAT_TAC;;

let mb_rel_del = cake_theorem "mb_rel_del"
  (fun () ->
    `!f refs_old refs v1 v2 ptr tag left ptr' right.
       mb_rel f refs_old refs v1 v2 /\
       FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag F left (RefPtr
         F ptr') right) /\ ~(
       ptr' IN FDOM refs) /\ ~(
       ptr' IN FDOM refs_old) /\ ~(
       ptr' IN FRANGE f) ==>
       mb_rel f refs_old (refs \\ ptr) v1 v2`)
  CHEAT_TAC;;

let state_ref_rel_update = cake_theorem "state_ref_rel_update"
  (fun () ->
    `!f s_refs t_refs ptr ptr' v w.
       state_ref_rel f s_refs t_refs /\ fmap_inj f /\
       FLOOKUP f ptr = SOME ptr' /\ bvi_tmcProof_ref_rel f v w ==>
       state_ref_rel f (s_refs |+ (ptr,v)) (t_refs |+ (ptr',w))`)
  CHEAT_TAC;;

let bvl_to_bvi_refs = cake_theorem "bvl_to_bvi_refs"
  (fun () ->
    `bvl_to_bvi (state_refs_fupd (K r) (bvi_to_bvl s)) s =
  state_refs_fupd (K r) s`)
  CHEAT_TAC;;

let holes_unchanged_except_frange_update =
  cake_theorem "holes_unchanged_except_frange_update"
  (fun () ->
    `!f p k v refs.
       FLOOKUP f p = SOME k ==>
       holes_unchanged_except f refs (refs |+ (k,v)) {}`)
  CHEAT_TAC;;

let holes_still_not_finalised_frange_update =
  cake_theorem "holes_still_not_finalised_frange_update"
  (fun () ->
    `!f p k v refs.
       FLOOKUP f p = SOME k ==>
       holes_still_not_finalised f refs (refs |+ (k,v))`)
  CHEAT_TAC;;

let ref_rel_submap = cake_theorem "ref_rel_submap"
  (fun () ->
    `!f f' v w. bvi_tmcProof_ref_rel f v w /\ f SUBMAP f' ==>
  bvi_tmcProof_ref_rel f' v w`)
  CHEAT_TAC;;

let state_ref_rel_alloc = cake_theorem "state_ref_rel_alloc"
  (fun () ->
    `!f s_refs t_refs src tgt rv rw.
       state_ref_rel f s_refs t_refs /\ ~(
       src IN FDOM s_refs) /\ ~(tgt IN FDOM t_refs) /\ ~(tgt IN
         FRANGE f) /\
       bvi_tmcProof_ref_rel (f |+ (src,tgt)) rv rw ==>
       state_ref_rel (f |+ (src,tgt)) (s_refs |+ (src,rv))
         (t_refs |+ (tgt,rw))`)
  CHEAT_TAC;;

let state_rel_alloc = cake_theorem "state_rel_alloc"
  (fun () ->
    `!f s s' src tgt rv rw.
       bvi_tmcProof_state_rel f s s' /\ ~(
       src IN FDOM (state_refs s)) /\ ~(tgt IN FDOM (state_refs
         s')) /\ ~(tgt IN FRANGE f) /\
       bvi_tmcProof_ref_rel (f |+ (src,tgt)) rv rw ==>
       FLOOKUP (f |+ (src,tgt)) src = SOME tgt /\
       bvi_tmcProof_state_rel (f |+ (src,tgt))
         (state_refs_fupd (K (state_refs s |+ (src,rv))) s)
           (state_refs_fupd (K (state_refs s' |+ (tgt,rw))) s') /\
       f SUBMAP f |+ (src,tgt) /\
       only_fresh f (f |+ (src,tgt)) (state_refs s') /\
       holes_unchanged_except f (state_refs s') (state_refs s' |+
         (tgt,rw)) {} /\
       holes_still_not_finalised f (state_refs s') (state_refs s'
         |+ (tgt,rw))`)
  CHEAT_TAC;;

let state_ref_rel_lookup = cake_theorem "state_ref_rel_lookup"
  (fun () ->
    `!f n m refs t_refs.
       FLOOKUP f n = SOME m /\ state_ref_rel f refs t_refs ==>
       (?v w. FLOOKUP refs n = SOME v /\ FLOOKUP t_refs m = SOME
         w /\ bvi_tmcProof_ref_rel f v w)`)
  CHEAT_TAC;;

let fmap_inj_flookup_eq = cake_theorem "fmap_inj_flookup_eq"
  (fun () ->
    `!f n m n' m'.
       fmap_inj f /\ FLOOKUP f n = SOME m /\ FLOOKUP f n' = SOME m'
         ==>
       ((m = m') <=> (n = n'))`)
  CHEAT_TAC;;

let v_to_list_v_rel = cake_theorem "v_to_list_v_rel"
  (fun () ->
    `!lv xs lw f.
       bvlSem_v_to_list lv = SOME xs /\ bvi_tmcProof_v_rel f lv lw
         ==>
       (?ys. bvlSem_v_to_list lw = SOME ys /\ LIST_REL
         (bvi_tmcProof_v_rel f) xs ys)`)
  CHEAT_TAC;;

let list_to_v_v_rel = cake_theorem "list_to_v_v_rel"
  (fun () ->
    `!xs ys f.
       LIST_REL (bvi_tmcProof_v_rel f) xs ys ==>
       bvi_tmcProof_v_rel f (list_to_v xs) (list_to_v ys)`)
  CHEAT_TAC;;

let do_eq_v_rel = cake_theorem "do_eq_v_rel"
  (fun () ->
    `(!refs x1 x2 t_refs y1 y2.
        bvi_tmcProof_v_rel f x1 y1 /\ bvi_tmcProof_v_rel f x2 y2 /\
          state_ref_rel f refs t_refs /\ fmap_inj f ==>
        do_eq refs x1 x2 = do_eq t_refs y1 y2) /\
     (!refs x1s x2s t_refs y1s y2s.
        LIST_REL (bvi_tmcProof_v_rel f) x1s y1s /\ LIST_REL
          (bvi_tmcProof_v_rel f) x2s y2s /\
        state_ref_rel f refs t_refs /\ fmap_inj f ==>
        do_eq_list refs x1s x2s = do_eq_list t_refs y1s y2s)`)
  CHEAT_TAC;;

let do_word_app_v_rel = cake_theorem "do_word_app_v_rel"
  (fun () ->
    `!w vs res vs' f.
       bvlSem_do_word_app w vs = SOME res /\ LIST_REL
         (bvi_tmcProof_v_rel f) vs vs' ==>
       vs' = vs`)
  CHEAT_TAC;;

let do_word_app_v_rel_refl = cake_theorem "do_word_app_v_rel_refl"
  (fun () ->
    `!w vs res f.
       bvlSem_do_word_app w vs = SOME res ==> bvi_tmcProof_v_rel
         f res res`)
  CHEAT_TAC;;

let no_mutblock = cake_theorem "no_mutblock"
  (fun () ->
    `!f refs t_refs ptr tag fin l c r.
       state_ref_rel f refs t_refs /\ FLOOKUP refs ptr = SOME
         (bvlSem_MutBlock tag fin l c r) ==> F`)
  CHEAT_TAC;;

(* Install reads byte/word vectors out of values; these are lists of Numbers
   resp. Word64s, which v_rel relates exactly. *)

let list_rel_v_rel_number = cake_theorem "list_rel_v_rel_number[local]"
  (fun () ->
    `!g ns ys f. LIST_REL (bvi_tmcProof_v_rel f) (MAP (Number o g) ns)
  ys ==> ys = MAP (Number o g) ns`)
  CHEAT_TAC;;

let list_rel_v_rel_word = cake_theorem "list_rel_v_rel_word[local]"
  (fun () ->
    `!ns ys f. LIST_REL (bvi_tmcProof_v_rel f) (MAP Word64 ns) ys ==>
  ys = MAP Word64 ns`)
  CHEAT_TAC;;

let bvi_tmcProof_v_to_bytes_eq = cake_theorem "v_to_bytes_eq[local]"
  (fun () ->
    `(v_to_bytes lv = SOME bytes) <=> (v_to_list lv = SOME (MAP
  (Number o (&) o w2n) bytes))`)
  CHEAT_TAC;;

let bvi_tmcProof_v_to_words_eq = cake_theorem "v_to_words_eq[local]"
  (fun () ->
    `(v_to_words lv = SOME ws) <=> (v_to_list lv = SOME (MAP Word64
  ws))`)
  CHEAT_TAC;;

let v_to_bytes_v_rel = cake_theorem "v_to_bytes_v_rel"
  (fun () ->
    `v_to_bytes lv = SOME bytes /\ bvi_tmcProof_v_rel f lv lw ==>
  v_to_bytes lw = SOME bytes`)
  CHEAT_TAC;;

let v_to_words_v_rel = cake_theorem "v_to_words_v_rel"
  (fun () ->
    `v_to_words lv = SOME ws /\ bvi_tmcProof_v_rel f lv lw ==>
  v_to_words lw = SOME ws`)
  CHEAT_TAC;;

let do_build_v_rel = cake_theorem "do_build_v_rel"
  (fun () ->
    `!parts' m i refs1 v refs1' f m' refs2.
       bvlSem_do_build m i parts' refs1 = (v,refs1') /\
         state_ref_rel f refs1 refs2 /\
       fmap_inj f /\ (!j. bvi_tmcProof_v_rel f (m j) (m' j)) ==>
       (?f' v' refs2'.
         bvlSem_do_build m' i parts' refs2 = (v',refs2') /\
           bvi_tmcProof_v_rel f' v v' /\
         state_ref_rel f' refs1' refs2' /\ fmap_inj f' /\ f SUBMAP
           f' /\
         only_fresh f f' refs2 /\ holes_unchanged_except f refs2
           refs2' {} /\
         holes_still_not_finalised f refs2 refs2')`)
  CHEAT_TAC;;

let do_build_const_v_rel = cake_theorem "do_build_const_v_rel"
  (fun () ->
    `!l refs1 v refs1' f refs2.
       bvlSem_do_build_const l refs1 = (v,refs1') /\ state_ref_rel
         f refs1 refs2 /\
       fmap_inj f ==>
       (?f' v' refs2'.
         bvlSem_do_build_const l refs2 = (v',refs2') /\
           bvi_tmcProof_v_rel f' v v' /\
         state_ref_rel f' refs1' refs2' /\ fmap_inj f' /\ f SUBMAP
           f' /\
         only_fresh f f' refs2 /\ holes_unchanged_except f refs2
           refs2' {} /\
         holes_still_not_finalised f refs2 refs2')`)
  CHEAT_TAC;;

let do_app_op_rel = cake_theorem "do_app_op_rel"
  (fun () ->
    `!f op vs vs' s s' t v.
       do_app op vs s = Rval (v,t) /\
       no_mutcons_op op /\
       LIST_REL (bvi_tmcProof_v_rel f) vs vs' /\
       bvi_tmcProof_state_rel f s s' ==>
       (?f' v' t'.
         do_app op vs' s' = Rval (v',t') /\
         bvi_tmcProof_v_rel f' v v' /\
         bvi_tmcProof_state_rel f' t t' /\
         f SUBMAP f' /\
         only_fresh f f' (state_refs s') /\
         holes_unchanged_except f (state_refs s') (state_refs t')
           {} /\
         holes_still_not_finalised f (state_refs s') (state_refs
           t'))`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:1520-1541: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1543-1549: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1551-1563: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1565-1593: a proof *)
  (* SetGlobal *)
(* HOL4 bvi_tmcProofScript.sml:1595-1616: a proof *)

(* Allocating a fresh reference (Ref, RefByte, RefArray). *)
(* HOL4 bvi_tmcProofScript.sml:1619-1640: a proof *)

(* Reading a reference without changing the state, returning a fresh value
   (Length, LengthByte, DerefByte, BoundsCheckArray, BoundsCheckByte). *)
(* HOL4 bvi_tmcProofScript.sml:1644-1650: a proof *)

(* Reading an element out of a ValueArray reference (El on a RefPtr). *)
(* HOL4 bvi_tmcProofScript.sml:1653-1662: a proof *)

(* Reading an element out of a Block (El on a Block). *)
(* HOL4 bvi_tmcProofScript.sml:1665-1670: a proof *)

(* Updating a ValueArray reference in place (Update). *)
(* HOL4 bvi_tmcProofScript.sml:1673-1689: a proof *)

(* Updating a ByteArray reference in place (UpdateByte, CopyByte, XorByte).
   The byte arrays are equal on both sides, so the operations agree. *)
(* HOL4 bvi_tmcProofScript.sml:1693-1703: a proof *)

(* Turning a stack of mutable conses into a Block (FinaliseCons). *)
(* HOL4 bvi_tmcProofScript.sml:1706-1713: a proof *)

(* Mutating the hole of a MutBlock (UpdateCons) cannot happen: state_ref_rel
   never relates a MutBlock. *)
(* HOL4 bvi_tmcProofScript.sml:1717-1719: a proof *)

(* ConfigGC returns Unit and leaves the state unchanged. *)
(* HOL4 bvi_tmcProofScript.sml:1722-1725: a proof *)

(* Comparing two ByteArray references without changing the state (StringCmp).
   Both byte arrays are equal on the two sides, so the comparison agrees. *)
(* HOL4 bvi_tmcProofScript.sml:1729-1734: a proof *)

let do_app_op_finalise_rel = cake_theorem "do_app_op_finalise_rel"
  (fun () ->
    `!v1 refs v1' v2 f s s'.
       finalise_cons v1 (state_refs s) = SOME (v2,refs) /\
       bvi_tmcProof_state_rel f s s' /\
       bvi_tmcProof_v_rel f v1 v1' ==>
       (?f' v2' refs'.
         finalise_cons v1' (state_refs s') = SOME (v2',refs') /\
         f SUBMAP f' /\
         bvi_tmcProof_v_rel f' v2 v2' /\
         bvi_tmcProof_state_rel f' (state_refs_fupd (K refs) s)
           (state_refs_fupd (K refs') s') /\
         only_fresh f f' (state_refs s') /\
         holes_unchanged_except f (state_refs s') refs' {} /\
         holes_still_not_finalised f (state_refs s') refs')`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:1768-1774: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1776-1784: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1786-1796: a proof *)

let dest_thunk_not_thunk_rel = cake_theorem "dest_thunk_not_thunk_rel"
  (fun () ->
    `!v v' refs refs' f.
       bvlSem_dest_thunk v refs = NotThunk /\
       bvi_tmcProof_v_rel f v v' /\
       state_ref_rel f refs refs' ==>
       bvlSem_dest_thunk v' refs' = NotThunk`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:1814-1817: a proof *)
   (* UpdateThunk *)
(* HOL4 bvi_tmcProofScript.sml:1819-1840: a proof *)
  (* AllocThunk *)
(* HOL4 bvi_tmcProofScript.sml:1842-1861: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1863-1884: a proof *)

(* Structural block operations with a fresh, state-preserving result
   (Cons, TagLenEq, LenEq, TagEq, LengthBlock, BoolTest, BoundsCheckBlock,
   EqualConst on a Number/Word64). *)
(* HOL4 bvi_tmcProofScript.sml:1889-1895: a proof *)

(* ElemAt reading an element out of a Block value. *)
(* HOL4 bvi_tmcProofScript.sml:1898-1905: a proof *)

(* ElemAt reading an element out of a ValueArray reference. *)
(* HOL4 bvi_tmcProofScript.sml:1908-1917: a proof *)

(* ConsExtend: result is an append of (a prefix of) two related blocks. *)
(* HOL4 bvi_tmcProofScript.sml:1920-1929: a proof *)

(* FromList: convert a list value to a packed Block. *)
(* HOL4 bvi_tmcProofScript.sml:1932-1938: a proof *)

(* ListAppend: append two lists. *)
(* HOL4 bvi_tmcProofScript.sml:1941-1945: a proof *)

(* Equal: structural equality preserved by the renaming (uses do_eq_v_rel). *)
(* HOL4 bvi_tmcProofScript.sml:1948-1956: a proof *)

(* EqualConst on a string constant (a compare-by-contents byte array). *)
(* HOL4 bvi_tmcProofScript.sml:1959-1966: a proof *)

(* Build: evaluate a constant, possibly allocating byte arrays for strings. *)
(* HOL4 bvi_tmcProofScript.sml:1969-1977: a proof *)

(* BoolNot: negates a boolean; the argument value is a Boolv, equal on both
   sides, so the negation agrees. *)
(* HOL4 bvi_tmcProofScript.sml:1981-1987: a proof *)

(* HOL4 bvi_tmcProofScript.sml:1989-1998: a proof *)

(* HOL4 bvi_tmcProofScript.sml:2000-2123: a proof *)

(* HOL4 bvi_tmcProofScript.sml:2125: a proof *)

let do_app_op_err_rel = cake_theorem "do_app_op_err_rel"
  (fun () ->
    `do_app (FFI i) vs u = Rerr (Rabort (Rffi_error e)) /\
     bvi_tmcProof_state_rel f u u' /\
     LIST_REL (bvi_tmcProof_v_rel f) vs vs' ==>
     do_app (FFI i) vs' u' = Rerr (Rabort (Rffi_error e))`)
  CHEAT_TAC;;

let wrapper_strip_if_then = cake_theorem "wrapper_strip_if_then"
  (fun () ->
    `rewrite_wrapper loc loc_opt n (If x1 x2 x3) = SOME w ==>
     (?w2 w3.
       w = If x1 w2 w3 /\
       (rewrite_wrapper loc loc_opt n x2 = SOME w2 \/
        w2 = x2))`)
  CHEAT_TAC;;

let wrapper_strip_if_else = cake_theorem "wrapper_strip_if_else"
  (fun () ->
    `rewrite_wrapper loc loc_opt n (If x1 x2 x3) = SOME w ==>
     (?w2 w3.
       w = If x1 w2 w3 /\
       (rewrite_wrapper loc loc_opt n x3 = SOME w3 \/
        w3 = x3))`)
  CHEAT_TAC;;

let wrapper_strip_let = cake_theorem "wrapper_strip_let"
  (fun () ->
    `!n loc loc_opt xs x w.
       rewrite_wrapper loc loc_opt n (Let xs x) = SOME w ==>
       (?w'.
         w = Let xs w' /\
         rewrite_wrapper loc loc_opt (n + LENGTH xs) x = SOME w')`)
  CHEAT_TAC;;

let wrapper_strip_tick = cake_theorem "wrapper_strip_tick"
  (fun () ->
    `!n loc loc_opt x w.
       rewrite_wrapper loc loc_opt n (Tick x) = SOME w ==>
       (?w'.
         w = Tick w' /\
         rewrite_wrapper loc loc_opt n x = SOME w')`)
  CHEAT_TAC;;

let is_block_op_cons_def = cake_define
  `is_block_op_cons op <=>
     (?block_tag.
       op = closLang_BlockOp (closLang_Cons block_tag))`;;

let bvi_tmcProof_bvi_to_bvl_refs = cake_theorem "bvi_to_bvl_refs"
  (fun () ->
    `state_refs
        (bvl_to_bvi s t) = state_refs s`)
  CHEAT_TAC;;

let finalise_cons_refs_SUBSET = cake_theorem "finalise_cons_refs_SUBSET"
  (fun () ->
    `!v1 refs1 v2 refs2.
       finalise_cons v1 refs1 = SOME (v2,refs2) ==>
       FDOM refs1 SUBSET FDOM refs2`)
  CHEAT_TAC;;

let bvi_tmcProof_do_app_refs_SUBSET = cake_theorem "do_app_refs_SUBSET"
  (fun () ->
    `(do_app op a r = Rval (q,t)) ==> FDOM (state_refs r) SUBSET FDOM
  (state_refs t)`)
  CHEAT_TAC;;

let bvi_tmcProof_evaluate_refs_SUBSET =
  cake_theorem "evaluate_refs_SUBSET"
  (fun () ->
    `!xs env s r t.
       (evaluate (xs,env,s) = (r,t)) ==> FDOM (state_refs s)
         SUBSET FDOM (state_refs t)`)
  CHEAT_TAC;;

let list_rel_reverse = cake_theorem "list_rel_reverse"
  (fun () ->
    `!r l1 l2. LIST_REL r l1 l2 <=> LIST_REL r (REVERSE l1) (REVERSE
  l2)`)
  CHEAT_TAC;;

let list_rel_last = cake_theorem "list_rel_last"
  (fun () ->
    `!r l1 l2.
       LIST_REL r l1 l2 /\ ~(
       l1 = []) ==>
       r (LAST l1) (LAST l2)`)
  CHEAT_TAC;;

let list_rel_front = cake_theorem "list_rel_front"
  (fun () ->
    `!r l1 l2.
       LIST_REL r l1 l2 ==>
       LIST_REL r (FRONT l1) (FRONT l2)`)
  CHEAT_TAC;;

let list_rel_env_rel = cake_theorem "list_rel_env_rel"
  (fun () ->
    `!f env1 env2.
       LIST_REL (bvi_tmcProof_v_rel f) env1 env2 ==>
       bvi_tmcProof_env_rel F f env1 env2`)
  CHEAT_TAC;;

let evaluate_fill_hole = cake_theorem "evaluate_fill_hole"
  (fun () ->
    `!exp f f' env1 env2 s t s' t' r r' c.
       evaluate ([exp],env1,s) = (r,t) /\
       evaluate ([exp],env2,s') = (r',t') /\
       bvi_tmcProof_env_rel T f env1 env2 /\
       bvi_tmcProof_state_rel f s s' /\
       f SUBMAP f' /\
       semanticPrimitivesProps_result_rel (LIST_REL
         (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
       hole_has_val f env1 env2 (state_refs s') c /\
       hole_not_finalised (state_refs s') hole_ptr /\
       holes_unchanged_except f (state_refs s') (state_refs t') {}
         /\
       holes_still_not_finalised f (state_refs s') (state_refs t')
         /\
       only_fresh f f' (state_refs s') /\
       bvi_tmcProof_state_rel f' t t' /\ EL (LENGTH env1)
       env2 = RefPtr F hole_ptr ==>
       (?r_fill f_fill t_fill.
         evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1)
           exp],env2,s') = (r_fill,t_fill) /\
         opt_res_rel f_fill r r_fill /\
         bvi_tmcProof_state_rel f_fill t t_fill /\
         f SUBMAP f_fill /\
         only_fresh f f_fill (state_refs s') /\
         holes_unchanged_except f (state_refs s') (state_refs
           t_fill) {hole_ptr} /\
         holes_still_not_finalised f (state_refs s') (state_refs
           t_fill) /\
         (!v.
           r = Rval [v] ==>
           (?v_fill.
             mb_rel f_fill (state_refs s') (state_refs t_fill \\
               hole_ptr) v v_fill /\
             hole_has_val f env1 env2 (state_refs t_fill)
               v_fill)))`)
  CHEAT_TAC;;

let evaluate_fill_hole_val = cake_theorem "evaluate_fill_hole_val"
  (fun () ->
    `!exp f f' env1 env2 s t s' t' v v' c.
       evaluate ([exp],env1,s) = (Rval [v],t) /\
       evaluate ([exp],env2,s') = (Rval [v'],t') /\
       bvi_tmcProof_env_rel T f env1 env2 /\
       bvi_tmcProof_state_rel f s s' /\
       f SUBMAP f' /\
       bvi_tmcProof_v_rel f' v v' /\
       hole_has_val f env1 env2 (state_refs s') c /\
       hole_not_finalised (state_refs s') hole_ptr /\
       holes_unchanged_except f (state_refs s') (state_refs t') {}
         /\
       holes_still_not_finalised f (state_refs s') (state_refs t')
         /\
       only_fresh f f' (state_refs s') /\
       bvi_tmcProof_state_rel f' t t' /\ EL (LENGTH env1)
       env2 = RefPtr F hole_ptr ==>
       (?r_fill f_fill t_fill.
         evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1)
           exp],env2,s') = (r_fill,t_fill) /\
         opt_res_rel f_fill (Rval [v]) r_fill /\
         bvi_tmcProof_state_rel f_fill t t_fill /\
         f SUBMAP f_fill /\
         only_fresh f f_fill (state_refs s') /\
         holes_unchanged_except f (state_refs s') (state_refs
           t_fill) {hole_ptr} /\
         holes_still_not_finalised f (state_refs s') (state_refs
           t_fill) /\
         (?v_fill.
           mb_rel f_fill (state_refs s') (state_refs t_fill \\
             hole_ptr) v v_fill /\
           hole_has_val f env1 env2 (state_refs t_fill) v_fill))`)
  CHEAT_TAC;;

let evaluate_vars_source = cake_theorem "evaluate_vars_source"
  (fun () ->
    `!vs env (s:(num#'c,'ffi)bviSem_state).
       wf_vars (LENGTH env) vs ==>
       evaluate (MAP (\n. Var n) vs,env,s) = (Rval (MAP (\n. EL n
         env) vs),s)`)
  CHEAT_TAC;;

let evaluate_vars_target = cake_theorem "evaluate_vars_target"
  (fun () ->
    `!vs n env (s:('c,'ffi)bviSem_state).
       wf_vars n vs /\
       LENGTH env >= n ==>
       evaluate (MAP (\n. Var n) vs,env,s) = (Rval (MAP (\n. EL n
         env) vs),s)`)
  CHEAT_TAC;;

let evaluate_vars_expand_env = cake_theorem "evaluate_vars_expand_env"
  (fun () ->
    `!vs env s v extras.
       evaluate (MAP (\n. Var n) vs,env,s) = (Rval v,s) ==>
       evaluate (MAP (\n. Var n) vs,env ++ extras,s) = (Rval v,s)`)
  CHEAT_TAC;;

let evaluate_var_list = cake_theorem "evaluate_var_list"
  (fun () ->
    `!ns env s t r.
       evaluate (MAP (\n. Var n) ns,env,s) = (r,t) /\ ~(
       r = Rerr (Rabort Rtype_error)) ==>
       (r,t) = (Rval (MAP (\n. EL n env) ns),s)`)
  CHEAT_TAC;;

let evaluate_var_list_binders = cake_theorem "evaluate_var_list_binders"
  (fun () ->
    `!ns extras env s r t.
       evaluate (MAP (\n. Var n) ns,env,s) = (r,t) /\ ~(
       r = Rerr (Rabort Rtype_error)) ==>
       evaluate (MAP (\n. Var (n + LENGTH extras)) ns,extras ++
         env,s) = (r,t)`)
  CHEAT_TAC;;

let evaluate_binders = cake_theorem "evaluate_binders"
  (fun () ->
    `!args env s t vs as next' next'.
       evaluate (args,env,s) = (Rval as,t) /\
       bvi_tmc_bind next' args = (vs,next') ==>
       (!ys.
         LENGTH ys = next' ==>
         evaluate (MAP (\n. Var n) vs,ys ++ as,t) = (Rval as,t))`)
  CHEAT_TAC;;

let evaluate_shift_vars = cake_theorem "evaluate_shift_vars"
  (fun () ->
    `!vs env s bs.
       evaluate (MAP (\n. Var n) (shift_vars (LENGTH bs) vs),bs ++
         env,s) =
       evaluate (MAP (\n. Var n) vs,env,s)`)
  CHEAT_TAC;;

let evaluate_shift_vars_sing = cake_theorem "evaluate_shift_vars_sing"
  (fun () ->
    `!vs env s b.
       evaluate (MAP (\n. Var n) (shift_vars 1 vs),b :: env,s) =
       evaluate (MAP (\n. Var n) vs,env,s)`)
  CHEAT_TAC;;

let evaluate_shift_cb = cake_theorem "evaluate_shift_cb"
  (fun () ->
    `!cb loc env s bs.
       evaluate ([cb_to_bvi loc (shift_cb (LENGTH bs) cb)],bs ++
         env,s) = evaluate ([cb_to_bvi loc cb],env,s)`)
  CHEAT_TAC;;

let evaluate_shift_cb_sing = cake_theorem "evaluate_shift_cb_sing"
  (fun () ->
    `!cb loc env s b.
       evaluate ([cb_to_bvi loc (shift_cb 1 cb)],b :: env,s) =
         evaluate ([cb_to_bvi loc cb],env,s)`)
  CHEAT_TAC;;

let evaluate_pure_exp_lemma =
  cake_theorem "evaluate_pure_exp_lemma[local]"
  (fun () ->
    `(!e n.
        pure_exp n e ==>
        (!env.
          n <= LENGTH env ==>
          (?v. !(s:('c,'ffi)bviSem_state). evaluate ([e],env,s) =
            (Rval v,s)))) /\
     (!(x:bvi_exp option). T) /\
     (!xs n.
        pure_exps n xs ==>
        (!env.
          n <= LENGTH env ==>
          (?v. !(s:('c,'ffi)bviSem_state). evaluate (xs,env,s) =
            (Rval v,s))))`)
  CHEAT_TAC;;

let evaluate_pure_exps = cake_theorem "evaluate_pure_exps"
  (fun () ->
    `!n xs.
       pure_exps n xs ==>
       (!env.
         n <= LENGTH env ==>
         (?v.
           !s.
             evaluate (xs,env,s) = (Rval v,s)))`)
  CHEAT_TAC;;

let evaluate_bvi_to_cb_aux_inl_lemma =
  cake_theorem "evaluate_bvi_to_cb_aux_inl_lemma[local]"
  (fun () ->
    `(!n loc tag exp bs vs.
        bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ==>
        bs = [exp] /\
        (!env.
          n <= LENGTH env ==>
          (?v.
            !(s:('c,'ffi)bviSem_state).
              evaluate ([exp],env,s) = (Rval v,s) /\
              evaluate (MAP (\n. Var n) vs,v,s) = (Rval v,s)))) /\
     (!n loc tag args bs vs.
        bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ==>
        bs = args /\
        (!env.
          n <= LENGTH env ==>
          (?v.
            !(s:('c,'ffi)bviSem_state).
              evaluate (args,env,s) = (Rval v,s) /\
              evaluate (MAP (\n. Var n) vs,v,s) = (Rval v,s))))`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:2708: a theorem that HOL4 states as
   the value of an ML expression *)

let evaluate_bvi_to_cb_aux_inr_lemma =
  cake_theorem "evaluate_bvi_to_cb_aux_inr_lemma[local]"
  (fun () ->
    `(!n loc tag exp env s t r bs cb.
        bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INR cb) /\
        evaluate ([Op (closLang_BlockOp (closLang_Cons tag))
          [exp]],env,
                  (s:('c,'ffi)bviSem_state)) = (r,t) /\
        n <= LENGTH env ==>
        (?as u.
          evaluate (bs,env,s) = (as,u) /\
          (!vs.
             as = Rval vs ==>
             evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
             (!extras.
               evaluate ([cb_to_bvi loc cb],vs ++ extras,u) =
                 (r,t))) /\
          (!e.
             as = Rerr e ==>
             (as,u) = (r,t)))) /\
     (!n loc tag args env s t r bs cb.
        bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) /\
        evaluate ([Op (closLang_BlockOp (closLang_Cons tag))
          args],env,
                  (s:('c,'ffi)bviSem_state)) = (r,t) /\
        n <= LENGTH env ==>
        (?as u.
          evaluate (bs,env,s) = (as,u) /\
          (!vs.
             as = Rval vs ==>
             evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) /\
             (!extras.
               evaluate ([cb_to_bvi loc cb],vs ++ extras,u) =
                 (r,t))) /\
          (!e.
             as = Rerr e ==>
             (as,u) = (r,t))))`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:2897: a theorem that HOL4 states as
   the value of an ML expression *)

let evaluate_bvi_to_cb = cake_theorem "evaluate_bvi_to_cb"
  (fun () ->
    `!cb n loc x env s t r bs.
       evaluate ([x],env,s) = (r,t) /\
       bvi_to_cb n loc x = SOME (bs,cb) /\
       n <= LENGTH env ==>
       evaluate ([Let bs (cb_to_bvi loc cb)],env,s) = (r,t)`)
  CHEAT_TAC;;

let WF_I_I = cake_theorem "WF_I_I[local]"
  (fun () ->
    `WF (MEASURE I LEX MEASURE I)`)
  CHEAT_TAC;;

let optimised_code_def = cake_define
  `optimised_code loc loc_opt c1 c2 <=>
     (?arity body body_wrap body_work.
       sptree_lookup loc c1 = SOME (arity,body) /\
       sptree_lookup loc c2 = SOME (arity,body_wrap) /\
       sptree_lookup loc_opt c2 = SOME (arity + 2,body_work) /\
       rewrite_wrapper loc loc_opt arity body = SOME body_wrap /\
       rewrite_worker loc loc_opt arity (arity + 1) arity body =
         body_work)`;;

let evaluate_rewrite_tmc = cake_theorem "evaluate_rewrite_tmc"
  (fun () ->
    `!n xs (s:(num#'c,'ffi)bviSem_state) env1 r t opt f s' env2 loc.
       evaluate (xs,env1,s) = (r,t) /\
       n = (state_clock s,list_size flatLang_exp_size xs) /\
       bvi_tmcProof_env_rel opt f env1 env2 /\ EVERY (\x.
         no_mutcons x) xs /\
       bvi_tmcProof_state_rel f s s' /\
       (opt ==> LENGTH xs = 1) /\ ~(
       r = Rerr (Rabort Rtype_error)) ==>
       (?t' f' r'.
         evaluate (xs,env2,s') = (r',t') /\
         semanticPrimitivesProps_result_rel (LIST_REL
           (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
         bvi_tmcProof_state_rel f' t t' /\
         f SUBMAP f' /\
         only_fresh f f' (state_refs s') /\
         holes_unchanged_except f (state_refs s') (state_refs t')
           {} /\
         holes_still_not_finalised f (state_refs s') (state_refs
           t') /\
         (!loc_opt.
            optimised_code loc loc_opt (state_code s) (state_code
              s') ==>
            (!wrap.
               LENGTH xs = 1 /\
               rewrite_wrapper loc loc_opt (LENGTH env1) (HD xs) =
                 SOME wrap ==>
               (?t_wrap f_wrap r_wrap.
                 evaluate ([wrap],env2,s') = (r_wrap,t_wrap) /\
                 semanticPrimitivesProps_result_rel (LIST_REL
                   (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r
                   r_wrap /\
                 bvi_tmcProof_state_rel f_wrap t t_wrap /\
                 f SUBMAP f_wrap /\
                 only_fresh f f_wrap (state_refs s') /\
                 holes_unchanged_except f (state_refs s')
                   (state_refs t_wrap) {} /\
                 holes_still_not_finalised f (state_refs s')
                   (state_refs t_wrap))) /\
            (opt ==>
             (!i j hole_ptr work.
                i = LENGTH env1 /\
                j = LENGTH env1 + 1 /\
                (?c. hole_has_val f env1 env2 (state_refs s') c) /\
                hole_not_finalised (state_refs s') hole_ptr /\
                rewrite_worker loc loc_opt i j (LENGTH env1) (HD
                  xs) = work /\ EL i
                env2 = RefPtr F hole_ptr ==>
                (?r_work f_work t_work.
                  evaluate ([work],env2,s') = (r_work,t_work) /\
                  opt_res_rel f_work r r_work /\
                  bvi_tmcProof_state_rel f_work t t_work /\
                  f SUBMAP f_work /\
                  only_fresh f f_work (state_refs s') /\
                  holes_unchanged_except f (state_refs s')
                    (state_refs t_work) {hole_ptr} /\
                  holes_still_not_finalised f (state_refs s')
                    (state_refs t_work) /\
                  (!res_v.
                    r = Rval [res_v] ==>
                    (?res_v'.
                      mb_rel f_work (state_refs s') (state_refs
                        t_work \\ hole_ptr) res_v res_v' /\
                      hole_has_val f env1 env2 (state_refs
                        t_work) res_v')))))))`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:3031-3106: a proof *)

let hypothesis_def = cake_define
  `hypothesis xs' (s'':(num#'c,'ffi)bviSem_state) clock <=> state_clock
   s'' < clock ==>
   (!env1' r' t' opt' f' s'3' env2' loc'.
             evaluate (xs',env1',s'') = (r',t') /\
             bvi_tmcProof_env_rel opt' f' env1' env2' /\ EVERY (\x.
               no_mutcons x) xs' /\
             bvi_tmcProof_state_rel f' s'' s'3' /\
             (opt' ==> LENGTH xs' = 1) /\ ~(
             r' = Rerr (Rabort Rtype_error)) ==>
             (?t'' f'' r''.
               evaluate (xs',env2',s'3') = (r'',t'') /\
               semanticPrimitivesProps_result_rel (LIST_REL
                 (bvi_tmcProof_v_rel f'')) (eor_rel f'') r' r'' /\
               bvi_tmcProof_state_rel f'' t' t'' /\ f' SUBMAP f'' /\
                 only_fresh f' f'' (state_refs s'3') /\
               holes_unchanged_except f' (state_refs s'3')
                 (state_refs t'') {} /\
               holes_still_not_finalised f' (state_refs s'3')
                 (state_refs t'') /\
               (!loc_opt.
                 optimised_code loc' loc_opt (state_code s'')
                   (state_code s'3') ==>
                 (!wrap.
                    LENGTH xs' = 1 /\
                    rewrite_wrapper loc' loc_opt (LENGTH env1') (HD
                      xs') = SOME wrap ==>
                    (?t_wrap f_wrap r_wrap.
                      evaluate ([wrap],env2',s'3') = (r_wrap,t_wrap)
                        /\
                      semanticPrimitivesProps_result_rel (LIST_REL
                        (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r'
                        r_wrap /\ bvi_tmcProof_state_rel f_wrap t'
                          t_wrap /\ f' SUBMAP f_wrap /\
                      only_fresh f' f_wrap (state_refs s'3') /\
                      holes_unchanged_except f' (state_refs s'3')
                        (state_refs t_wrap) {} /\
                      holes_still_not_finalised f' (state_refs s'3')
                        (state_refs t_wrap))) /\
                 (opt' ==>
                  (!hole_ptr.
                    (?c. hole_has_val f' env1' env2' (state_refs
                      s'3') c) /\
                    hole_not_finalised (state_refs s'3') hole_ptr /\
                      EL (LENGTH env1')
                    env2' = RefPtr F hole_ptr ==>
                    (?r_work f_work t_work.
                      evaluate
                        ([rewrite_worker loc' loc_opt (LENGTH env1')
                            (LENGTH env1' + 1) (LENGTH env1') (HD
                              xs')],env2',s'3') =
                      (r_work,t_work) /\ opt_res_rel f_work r' r_work
                        /\
                      bvi_tmcProof_state_rel f_work t' t_work /\ f'
                        SUBMAP f_work /\
                      only_fresh f' f_work (state_refs s'3') /\
                      holes_unchanged_except f' (state_refs s'3')
                        (state_refs t_work) {hole_ptr} /\
                      holes_still_not_finalised f' (state_refs s'3')
                        (state_refs t_work) /\
                      (!res_v.
                        r' = Rval [res_v] ==>
                        (?res_v'.
                          mb_rel f_work (state_refs s'3') (state_refs
                            t_work \\ hole_ptr) res_v res_v' /\
                          hole_has_val f' env1' env2' (state_refs
                            t_work) res_v'))))))))`;;

let alloc_hole_has_val_def = cake_define
  `alloc_hole_has_val f refs extras i_ptr c_idx c <=>
     (?hole_ptr tag left right.
       i_ptr < LENGTH extras /\ EL i_ptr
       extras = RefPtr F hole_ptr /\
       c_idx = LENGTH left /\
       small_enough_int (&(LENGTH left)) /\ ~(
       hole_ptr IN FRANGE f) /\
       FLOOKUP refs hole_ptr = SOME (bvlSem_MutBlock tag F left c
         right))`;;

let wf_vars_list_rel = cake_theorem "wf_vars_list_rel"
  (fun () ->
    `!vars' opt f env1 env2.
       bvi_tmcProof_env_rel opt f env1 env2 /\
       wf_vars (LENGTH env1) vars' ==>
       LIST_REL (bvi_tmcProof_v_rel f) (MAP (\n. EL n env1)
         vars') (MAP (\n. EL n env2) vars')`)
  CHEAT_TAC;;

let wf_vars_env_rel = cake_theorem "wf_vars_env_rel"
  (fun () ->
    `!vars' opt f env1 env2.
       bvi_tmcProof_env_rel opt f env1 env2 /\
       wf_vars (LENGTH env1) vars' ==>
       bvi_tmcProof_env_rel F f (MAP (\n. EL n env1) vars') (MAP
         (\n. EL n env2) vars')`)
  CHEAT_TAC;;

let wf_vars_env_rel_opt = cake_theorem "wf_vars_env_rel_opt"
  (fun () ->
    `!vars' opt f env1 env2 ptr idx.
       bvi_tmcProof_env_rel opt f env1 env2 /\
       wf_vars (LENGTH env1) vars' /\
       small_enough_int idx ==>
       bvi_tmcProof_env_rel T f (MAP (\n. EL n env1) vars') (MAP
         (\n. EL n env2) vars' ++ [RefPtr F ptr; Number idx])`)
  CHEAT_TAC;;

let state_ref_rel_sub = cake_theorem "state_ref_rel_sub"
  (fun () ->
    `!ptr f s_refs t_refs. ~(
       ptr IN FRANGE f) /\
       state_ref_rel f s_refs t_refs ==>
       state_ref_rel f s_refs (t_refs \\ ptr)`)
  CHEAT_TAC;;

let holes_unchanged_except_finalised =
  cake_theorem "holes_unchanged_except_finalised"
  (fun () ->
    `(!f p ptr r1 r2 tag fin1 left child right fin2.
       holes_unchanged_except f (r1 \\ ptr) r2 EMPTY /\
       FLOOKUP r1 ptr = SOME (bvlSem_MutBlock tag fin1 left child
         right) /\ ~(
       ptr IN FRANGE f) ==>
       holes_unchanged_except f r1 r2 |+ (ptr,bvlSem_MutBlock tag
         fin2 left child right)) EMPTY`)
  CHEAT_TAC;;

let holes_still_not_finalised_sub =
  cake_theorem "holes_still_not_finalised_sub"
  (fun () ->
    `~(
       ptr IN FDOM refs) /\
       holes_still_not_finalised f refs refs' ==>
       holes_still_not_finalised f refs (refs' \\ ptr)`)
  CHEAT_TAC;;

let holes_still_not_finalised_non_dom =
  cake_theorem "holes_still_not_finalised_non_dom"
  (fun () ->
    `!f refs refs' ptr tag l c r.
       holes_still_not_finalised f refs refs' /\ ~(
       ptr IN FDOM refs) ==>
       holes_still_not_finalised f refs refs' |+
         (ptr,bvlSem_MutBlock tag T l c r)`)
  CHEAT_TAC;;

let evaluate_finalise_cons = cake_theorem "evaluate_finalise_cons"
  (fun () ->
    `!v2 t_refs (f:(num,num)fmap) f' u_refs v1 (s_refs:(num,bvlSem_v
  bvlSem_ref)fmap).
       state_ref_rel f' u_refs t_refs /\
       mb_rel f' s_refs t_refs v1 v2 /\
       holes_still_not_finalised f s_refs t_refs ==>
       (?v3 t_refs'.
         finalise_cons v2 t_refs = SOME (v3,t_refs') /\
         bvi_tmcProof_v_rel f' v1 v3 /\
         state_ref_rel f' u_refs t_refs' /\
         holes_unchanged_except f' t_refs t_refs' EMPTY /\
         holes_still_not_finalised f s_refs t_refs')`)
  CHEAT_TAC;;

let code_rel_cases = cake_theorem "code_rel_cases"
  (fun () ->
    `!loc arity body1 c1 c2.
       sptree_lookup loc c1 = SOME (arity,body1) /\
       bvi_tmcProof_code_rel c1 c2 ==>
       no_mutcons body1 /\
       (?loc_opt body2.
         sptree_lookup loc c2 = SOME (arity,body2) /\
         (~(body1 = body2) ==>
          optimised_code loc loc_opt c1 c2 /\
          rewrite_wrapper loc loc_opt arity body1 = SOME body2))`)
  CHEAT_TAC;;

let cons_append = cake_theorem "cons_append"
  (fun () ->
    `!v l.
       v :: l = [v] ++ l`)
  CHEAT_TAC;;

let rw_block_args = cake_theorem "rw_block_args"
  (fun () ->
    `!left child right f.
       REVERSE (MAP f left ++ [child] ++ MAP f right) = MAP f
         (REVERSE right) ++ [child] ++ MAP f (REVERSE left)`)
  CHEAT_TAC;;

let shift_cb_suc = cake_theorem "shift_cb_suc"
  (fun () ->
    `!n cb.
       shift_cb (SUC (SUC n)) cb = shift_cb (n + 2) cb`)
  CHEAT_TAC;;

let mb_rel_refs_old_subset = cake_theorem "mb_rel_refs_old_subset"
  (fun () ->
    `!f r2 r3 v1 v2 r1.
       mb_rel f r2 r3 v1 v2 /\
       (FDOM r1) SUBSET (FDOM r2) ==>
       mb_rel f r1 r3 v1 v2`)
  CHEAT_TAC;;

let evaluate_cb = cake_theorem "evaluate_cb"
  (fun () ->
    `!cb loc f opt env env2 (s:(num#'c,'ffi)bviSem_state) s' t r clock.
       evaluate ([cb_to_bvi loc cb],env,s) = (r,t) /\
       wf_cb (LENGTH env) cb /\
       bvi_tmcProof_env_rel opt f env env2 /\
       bvi_tmcProof_state_rel f s s' /\ state_clock
       s <= clock /\ ~(
       r = Rerr (Rabort Rtype_error)) /\
       (!xs' (s'':(num#'c,'ffi)bviSem_state).
          hypothesis xs' s'' clock) ==>
       (?r' t' f'.
          evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') /\
          semanticPrimitivesProps_result_rel (LIST_REL
            (bvi_tmcProof_v_rel f')) (eor_rel f') r r' /\
          bvi_tmcProof_state_rel f' t t' /\
          f SUBMAP f' /\
          only_fresh f f' (state_refs s') /\
          holes_unchanged_except f (state_refs s') (state_refs t')
            {} /\
          holes_still_not_finalised f (state_refs s') (state_refs
            t')) /\
       (!loc_opt.
         optimised_code loc loc_opt (state_code s) (state_code s')
           ==>
         (!tag left child right.
            cb = CallBlock tag left child right ==>
            (?t_wrap f_wrap r_wrap.
              evaluate ([cb_to_bvi_wrapper tag left child right
                loc_opt],env2,s') = (r_wrap,t_wrap) /\
              semanticPrimitivesProps_result_rel (LIST_REL
                (bvi_tmcProof_v_rel f_wrap)) (eor_rel f_wrap) r r_wrap
                /\
              bvi_tmcProof_state_rel f_wrap t t_wrap /\
              f SUBMAP f_wrap /\
              only_fresh f f_wrap (state_refs s') /\
              holes_unchanged_except f (state_refs s') (state_refs
                t_wrap) {} /\
              holes_still_not_finalised f (state_refs s')
                (state_refs t_wrap))) /\
         (!refs extras ptr idx hole_ptr.
            state_ref_rel f (state_refs s) refs /\
            (?c. alloc_hole_has_val f refs extras ptr idx c) /\
            (FDOM (state_refs s')) SUBSET (FDOM refs) /\
            EL ptr extras = RefPtr F hole_ptr ==>
            (?r_aux t_aux f_aux.
              evaluate ([cb_to_bvi_worker_aux (shift_cb (LENGTH
                extras) cb) loc_opt ptr idx],extras ++
                env2,state_refs_fupd (K refs) s') = (r_aux,t_aux) /\
              opt_res_rel f_aux r r_aux /\
              bvi_tmcProof_state_rel f_aux t t_aux /\
              f SUBMAP f_aux /\
              only_fresh f f_aux refs /\
              holes_unchanged_except f refs (state_refs t_aux)
                {hole_ptr} /\
              holes_still_not_finalised f refs (state_refs t_aux)
                /\
              (!res_v.
                r = Rval [res_v] ==>
                (?res_v'.
                  mb_rel f_aux (state_refs s') (state_refs t_aux \\
                    hole_ptr) res_v res_v' /\
                  alloc_hole_has_val f (state_refs t_aux) extras
                    ptr idx res_v')))) /\
         (opt ==>
          (!ptr idx work hole_ptr.
             ptr = LENGTH env /\
             idx = LENGTH env + 1 /\
             (?c. hole_has_val f env env2 (state_refs s') c) /\
             hole_not_finalised (state_refs s') hole_ptr /\
             EL ptr env2 = RefPtr F hole_ptr ==>
             (?r_work f_work t_work.
               evaluate ([cb_to_bvi_worker cb loc_opt ptr
                 idx],env2,s') = (r_work,t_work) /\
               opt_res_rel f_work r r_work /\
               bvi_tmcProof_state_rel f_work t t_work /\
               f SUBMAP f_work /\
               only_fresh f f_work (state_refs s') /\
               holes_unchanged_except f (state_refs s') (state_refs
                 t_work) {hole_ptr} /\
               holes_still_not_finalised f (state_refs s')
                 (state_refs t_work) /\
               (!res_v.
                 r = Rval [res_v] ==>
                 (?res_v'.
                   mb_rel f_work (state_refs s') (state_refs t_work
                     \\ hole_ptr) res_v res_v' /\
                   hole_has_val f env env2 (state_refs t_work)
                     res_v'))))))`)
  CHEAT_TAC;;

let evaluate_pres_opt_code = cake_theorem "evaluate_pres_opt_code"
  (fun () ->
    `!loc loc_opt s1 s2 xs env1 env2 r1 u1 r2 u2.
       optimised_code loc loc_opt (state_code s1) (state_code s2)
         /\
       evaluate (xs,env1,s1) = (r1,u1) /\
       evaluate (xs,env2,s2) = (r2,u2) ==>
       optimised_code loc loc_opt (state_code u1) (state_code u2)`)
  CHEAT_TAC;;

let bvi_to_cb_aux_no_mutcons_lemma =
  cake_theorem "bvi_to_cb_aux_no_mutcons_lemma[local]"
  (fun () ->
    `(!n loc tag exp cb bs.
        bvi_to_cb_aux_sing n loc tag exp = SOME (bs,cb) /\
        no_mutcons (Op (closLang_BlockOp (closLang_Cons tag))
          [exp]) ==>
        EVERY (\x. no_mutcons x) bs) /\
     (!n loc tag args cb bs.
        bvi_to_cb_aux n loc tag args = SOME (bs,cb) /\
        no_mutcons (Op (closLang_BlockOp (closLang_Cons tag)) args)
          ==>
        EVERY (\x. no_mutcons x) bs)`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:4193: a theorem that HOL4 states as
   the value of an ML expression *)

let bvi_to_cb_no_mutcons = cake_theorem "bvi_to_cb_no_mutcons"
  (fun () ->
    `!cb bs n loc x.
       bvi_to_cb n loc x = SOME (bs,cb) /\
       no_mutcons x ==>
       EVERY (\x. no_mutcons x) bs`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:4209: a proof *)
  (* Phase 1 theorem in s *)
(* HOL4 bvi_tmcProofScript.sml:4211-4216: a proof *)
  (* Hypothesis on bs *)
(* HOL4 bvi_tmcProofScript.sml:4218-4231: a proof *)
  (* Phase 1 theorem in s' *)
(* HOL4 bvi_tmcProofScript.sml:4233-4263: a proof *)
  (* Phase 2 theorem *)
(* HOL4 bvi_tmcProofScript.sml:4265-4418: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4420-4421: a proof *)
  (* First inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4423-4439: a proof *)
  (* Second inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4441-4488: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4490-4513: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4515-4518: a proof *)
  (* First inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4520-4652: a proof *)
    (* Else inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4654-4768: a proof *)
  (* Error case *)
(* HOL4 bvi_tmcProofScript.sml:4770-4792: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4794-4797: a proof *)
  (* First inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4799-4829: a proof *)
  (* Second inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:4831-4936: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4938-4975: a proof *)

(* HOL4 bvi_tmcProofScript.sml:4977-5026: a proof *)

let find_code_rel = cake_theorem "find_code_rel"
  (fun () ->
    `!f vs vs' s s' dest args body.
       find_code dest vs (state_code s) = SOME (args,body) /\
       LIST_REL (bvi_tmcProof_v_rel f) vs vs' /\
       bvi_tmcProof_state_rel f s s' ==>
       no_mutcons body /\
       (?args' body' loc.
         find_code dest vs' (state_code s') = SOME (args',body') /\
         bvi_tmcProof_env_rel F f args args' /\
         LENGTH args = LENGTH args' /\
         (~(body = body') ==>
          (?loc_opt.
            optimised_code loc loc_opt (state_code s) (state_code
              s') /\
            rewrite_wrapper loc loc_opt (LENGTH args) body = SOME
              body')))`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:5091-5095: a proof *)
  (* xs inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:5097-5111: a proof *)
  (* Error case *)
(* HOL4 bvi_tmcProofScript.sml:5113-5445: a proof *)

let dest_thunk_ret_rel_def = cake_define
  `dest_thunk_ret_rel f t1 t2 <=>
     ((t1 = BadRef /\ t2 = BadRef) \/
      (t1 = NotThunk /\ t2 = NotThunk) \/
      (?tm1 tm2 v1 v2.
        t1 = IsThunk tm1 v1 /\ t2 = IsThunk tm2 v2 /\
        tm1 = tm2 /\
        bvi_tmcProof_v_rel f v1 v2))`;;

let env_rel_el = cake_theorem "env_rel_el"
  (fun () ->
    `!opt f env1 env2 n.
       bvi_tmcProof_env_rel opt f env1 env2 /\
       n < LENGTH env1 ==>
       bvi_tmcProof_v_rel f (EL n env1) (EL n env2)`)
  CHEAT_TAC;;

let dest_thunk_rel = cake_theorem "dest_thunk_rel"
  (fun () ->
    `!opt f env1 env2 s1 s2 n.
       bvi_tmcProof_env_rel opt f env1 env2 /\
       bvi_tmcProof_state_rel f s1 s2 /\
       n < LENGTH env1 ==>
       dest_thunk_ret_rel f (dest_thunk (EL n env1) (state_refs
         s1)) (dest_thunk (EL n env2) (state_refs s2))`)
  CHEAT_TAC;;

(* HOL4 bvi_tmcProofScript.sml:5496-5594: a proof *)

(* HOL4 bvi_tmcProofScript.sml:5596-5599: a proof *)
  (* args inductive hypothesis *)
(* HOL4 bvi_tmcProofScript.sml:5601-5645: a proof *)
      (* callee inductive hypothesis (smaller clock) *)
(* HOL4 bvi_tmcProofScript.sml:5647-5744: a proof *)
          (* the wrapper-IH gives the target callee result for body'; rename to
             controlled names and discard the spurious direct-IH result for exp *)
(* HOL4 bvi_tmcProofScript.sml:5747-5831: a proof *)

(* HOL4 bvi_tmcProofScript.sml:5833-5869: a proof *)

(* HOL4 bvi_tmcProofScript.sml:5871: a proof *)

let bvi_tmcProof_evaluate_compile_each =
  cake_theorem "evaluate_compile_each"
  (fun () ->
    `bvi_tmcProof_input_condition next' prog /\
     (!n next' cfg prog. co n = ((next',cfg),prog) ==>
       bvi_tmcProof_input_condition next' prog) /\
     (!n. MEM n (MAP FST (SND (bvi_tmc_compile_each next' prog)))
       /\ (\n. n MOD bvl_to_bvi_namespaces = 3) n ==> n < FST (FST (co
       0))) /\
     evaluate ([Call 0 (SOME start) [] NONE],[],
               initial_state ffi0 (fromAList prog) co
                   (state_cc bvi_tmc_compile_each cc) k) = (r,s) /\
                     ~(
     r = Rerr (Rabort Rtype_error)) ==>
     (?f s2 r2.
       evaluate
        ([Call 0 (SOME start) [] NONE],[],
          initial_state ffi0 (fromAList (SND (bvi_tmc_compile_each
            next' prog)))
              (state_co bvi_tmc_compile_each co) cc k) = (r2,s2) /\
       semanticPrimitivesProps_result_rel (LIST_REL
         (bvi_tmcProof_v_rel f)) (eor_rel f) r r2 /\
       bvi_tmcProof_state_rel f s s2)`)
  CHEAT_TAC;;

let bvi_tmcProof_state_rel_const = cake_theorem "state_rel_const"
  (fun () ->
    `bvi_tmcProof_state_rel f s t ==> state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_semantics =
  cake_theorem "compile_each_semantics"
  (fun () ->
    `bvi_tmcProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==>
       bvi_tmcProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ (\n. n MOD bvl_to_bvi_namespaces
       = 3) k ==> k < FST (FST (co 0))) /\
     SND (bvi_tmc_compile_each n prog) = prog2 /\ ~(
     semantics ffi (fromAList prog) co (state_cc
       bvi_tmc_compile_each cc) start = ffi_Fail) ==>
     semantics ffi (fromAList prog) co (state_cc
       bvi_tmc_compile_each cc) start =
     semantics ffi (fromAList prog2) (state_co
       bvi_tmc_compile_each co) cc start`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_prog_semantics =
  cake_theorem "compile_prog_semantics"
  (fun () ->
    `bvi_tmcProof_input_condition n prog /\
     (!k n cfg prog. co k = ((n,cfg),prog) ==>
       bvi_tmcProof_input_condition n prog) /\
     (!k. MEM k (MAP FST prog2) /\ (\n. n MOD bvl_to_bvi_namespaces
       = 3) k ==> k < FST (FST (co 0))) /\
     SND (compile_prog b n prog) = prog2 /\ ~(
     semantics ffi (fromAList prog) co (state_cc (compile_prog b)
       cc) start =
       ffi_Fail) ==>
     semantics ffi (fromAList prog) co (state_cc (compile_prog b)
       cc) start =
     semantics ffi (fromAList prog2) (state_co (compile_prog b)
       co) cc start`)
  CHEAT_TAC;;

(* -------------------------------------------------------------------------
   Code labels: the pass only introduces calls to the fresh worker names it
   allocates, so every label of the output is a label of the input or one of
   the names strictly below the final next-name.
   ------------------------------------------------------------------------- *)

let get_code_labels_MAP_Var =
  cake_theorem "get_code_labels_MAP_Var[local,simp]"
  (fun () ->
    `BIGUNION (set_of_list (MAP get_code_labels' (MAP (\n. Var n)
  vs))) = {}`)
  CHEAT_TAC;;

let cb_to_bvi_worker_aux_code_labels =
  cake_theorem "cb_to_bvi_worker_aux_code_labels[local]"
  (fun () ->
    `!cb loc_opt ptr idx.
       get_code_labels (cb_to_bvi_worker_aux cb loc_opt ptr idx)
         = {loc_opt}`)
  CHEAT_TAC;;

let cb_to_bvi_worker_code_labels =
  cake_theorem "cb_to_bvi_worker_code_labels[local]"
  (fun () ->
    `get_code_labels (cb_to_bvi_worker cb loc_opt ptr idx) = {loc_opt}`)
  CHEAT_TAC;;

let cb_to_bvi_wrapper_code_labels =
  cake_theorem "cb_to_bvi_wrapper_code_labels[local]"
  (fun () ->
    `get_code_labels (cb_to_bvi_wrapper tag left child right loc_opt)
  = {loc_opt}`)
  CHEAT_TAC;;

let bvi_to_cb_aux_code_labels_lemma =
  cake_theorem "bvi_to_cb_aux_code_labels_lemma[local]"
  (fun () ->
    `(!n loc tag exp bs r.
        bvi_to_cb_aux_sing n loc tag exp = SOME (bs,r) ==>
        BIGUNION (set_of_list (MAP get_code_labels bs)) SUBSET
          get_code_labels exp) /\
     (!n loc tag args bs r.
        bvi_to_cb_aux n loc tag args = SOME (bs,r) ==>
        BIGUNION (set_of_list (MAP get_code_labels bs)) SUBSET
        BIGUNION (set_of_list (MAP get_code_labels args)))`)
  CHEAT_TAC;;

let bvi_to_cb_code_labels = cake_theorem "bvi_to_cb_code_labels[local]"
  (fun () ->
    `!n loc exp bs cb.
       bvi_to_cb n loc exp = SOME (bs,cb) ==>
       BIGUNION (set_of_list (MAP get_code_labels bs)) SUBSET
         get_code_labels exp`)
  CHEAT_TAC;;

let rewrite_wrapper_code_labels =
  cake_theorem "rewrite_wrapper_code_labels[local]"
  (fun () ->
    `!loc loc_opt n exp y.
       rewrite_wrapper loc loc_opt n exp = SOME y ==>
       get_code_labels y SUBSET get_code_labels exp UNION
         {loc_opt}`)
  CHEAT_TAC;;

let rewrite_worker_code_labels =
  cake_theorem "rewrite_worker_code_labels[local]"
  (fun () ->
    `!loc loc_opt p i n exp.
       get_code_labels (rewrite_worker loc loc_opt p i n exp)
         SUBSET
       get_code_labels exp UNION {loc_opt}`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_exp_code_labels =
  cake_theorem "compile_exp_code_labels[local]"
  (fun () ->
    `compile_exp loc next arity exp = SOME (exp_w,exp_k) ==>
     get_code_labels exp_w SUBSET get_code_labels exp UNION {next}
       /\
     get_code_labels exp_k SUBSET get_code_labels exp UNION
       {next}`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_good_code_labels =
  cake_theorem "compile_each_good_code_labels"
  (fun () ->
    `!n c n2 c2.
       bvi_tmc_compile_each n c = (n2,c2) /\
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND) c))
         SUBSET all /\
       {n + k * bvl_to_bvi_namespaces | k | n + k *
         bvl_to_bvi_namespaces < n2} SUBSET all ==>
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         c2)) SUBSET all`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_prog_good_code_labels =
  cake_theorem "compile_prog_good_code_labels"
  (fun () ->
    `!b n c n2 c2.
       compile_prog b n c = (n2,c2) /\
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND) c))
         SUBSET all /\
       {n + k * bvl_to_bvi_namespaces | k | n + k *
         bvl_to_bvi_namespaces < n2} SUBSET all ==>
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         c2)) SUBSET all`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_each_keeps_names =
  cake_theorem "compile_each_keeps_names"
  (fun () ->
    `!next' xs next' ys.
       bvi_tmc_compile_each next' xs = (next',ys) /\ MEM x (MAP FST
         xs) ==>
       MEM x (MAP FST ys)`)
  CHEAT_TAC;;

let bvi_tmcProof_compile_prog_keeps_names =
  cake_theorem "compile_prog_keeps_names"
  (fun () ->
    `!b next' xs next' ys.
       compile_prog b next' xs = (next',ys) /\ MEM x (MAP FST xs)
         ==>
       MEM x (MAP FST ys)`)
  CHEAT_TAC;;
