(* ======================================================== *)
(*  bvi_inlineProof: ported from HOL4's
    compiler/backend/proofs/bvi_inlineProofScript.sml
    A proof theory about bvi_inline.ml, with 9 definitions and 70
    theorems.  Needed by backendProof.ml and bvl_to_bviProof.ml.  *)
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
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["error"];;

let inline_exps_LENGTH = cake_theorem "inline_exps_LENGTH[simp]"
  (fun () ->
    `!cs es. LENGTH (inline_exps cs es) = LENGTH es`)
  CHEAT_TAC;;

let remove_ticks_exps_LENGTH =
  cake_theorem "remove_ticks_exps_LENGTH[simp]"
  (fun () ->
    `!es. LENGTH (remove_ticks_exps es) = LENGTH es`)
  CHEAT_TAC;;

let inline_exps_CONS = cake_theorem "inline_exps_CONS[simp]"
  (fun () ->
    `inline_exps cs (x :: xs) = inline_exp cs x :: inline_exps cs xs`)
  CHEAT_TAC;;

let inline_exps_MAP = cake_theorem "inline_exps_MAP"
  (fun () ->
    `!cs es. inline_exps cs es = MAP (inline_exp cs) es`)
  CHEAT_TAC;;

let inline_exps_REVERSE = cake_theorem "inline_exps_REVERSE[simp]"
  (fun () ->
    `!cs es. inline_exps cs (REVERSE es) = REVERSE (inline_exps cs es)`)
  CHEAT_TAC;;

let inline_exps_MAP_Var = cake_theorem "inline_exps_MAP_Var[simp]"
  (fun () ->
    `!cs ns. inline_exps cs (MAP Var ns) = MAP Var ns`)
  CHEAT_TAC;;

let inline_exps_GENLIST_Var =
  cake_theorem "inline_exps_GENLIST_Var[simp]"
  (fun () ->
    `!cs n. inline_exps cs (GENLIST Var n) = GENLIST Var n`)
  CHEAT_TAC;;

let incremental_wrapper_example =
  cake_theorem "incremental_wrapper_example"
  (fun () ->
    `?cs p1 p2.
       compile_inc LN
         [(10,0,bvi_LetCall 0 0 11 []
           (bvi_Op (closLang_BlockOp (closLang_Cons 7)) []))] =
             (cs,p1) /\
       compile_inc cs
         [(12,0,Call 0 (SOME 10) [] NONE)] = (cs,p2) /\
       p2 = [(12,0,
         Let [] (bvi_LetCall 0 0 11 [] (bvi_Op (closLang_BlockOp
           (closLang_Cons 7)) [])))]`)
  CHEAT_TAC;;

let canonical_wrapper_thm = cake_theorem "canonical_wrapper_thm"
  (fun () ->
    `!name arity body.
       canonical_wrapper name arity body <=>
         (?rets ticks worker tag. ~(worker = name) /\
           body =
             bvi_LetCall rets ticks worker (GENLIST bvi_Var arity)
               (bvi_Op (closLang_BlockOp (closLang_Cons tag))
                  (REVERSE (GENLIST bvi_Var rets))))`)
  CHEAT_TAC;;

let wrapper_ok_inline_exp = cake_theorem "wrapper_ok_inline_exp[simp]"
  (fun () ->
    `wrapper_ok name arity body ==> inline_exp cs body = body`)
  CHEAT_TAC;;

let inline_all_MAP_FST = cake_theorem "inline_all_MAP_FST"
  (fun () ->
    `!cs prog. MAP FST (SND (inline_all cs prog)) = MAP FST prog`)
  CHEAT_TAC;;

let MAP_FST_remove_ticks_prog =
  cake_theorem "MAP_FST_remove_ticks_prog[simp]"
  (fun () ->
    `!prog.
       MAP FST (MAP (\(name,arity,body).
         (name,arity,remove_ticks_exp body)) prog) = MAP FST prog`)
  CHEAT_TAC;;

let compile_inc_MAP_FST = cake_theorem "compile_inc_MAP_FST"
  (fun () ->
    `compile_inc cs prog = (cs1,prog1) ==> MAP FST prog1 = MAP FST
  prog`)
  CHEAT_TAC;;

let compile_inc_ALL_DISTINCT = cake_theorem "compile_inc_ALL_DISTINCT"
  (fun () ->
    `compile_inc cs prog = (cs1,prog1) /\ ALL_DISTINCT (MAP FST prog)
  ==>
     ALL_DISTINCT (MAP FST prog1)`)
  CHEAT_TAC;;

let remove_ticks_get_code_labels =
  cake_theorem "remove_ticks_get_code_labels"
  (fun () ->
    `(!e. get_code_labels (remove_ticks_exp e) = get_code_labels e) /\
     (!es. BIGUNION (set_of_list (MAP get_code_labels
       (remove_ticks_exps es))) =
           BIGUNION (set_of_list (MAP get_code_labels es)))`)
  CHEAT_TAC;;

let remove_ticks_prog_code_labels =
  cake_theorem "remove_ticks_prog_code_labels"
  (fun () ->
    `!prog.
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         (MAP (\(name,arity,body).
           (name,arity,remove_ticks_exp body)) prog))) =
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         prog))`)
  CHEAT_TAC;;

let compile_inc_code_labels = cake_theorem "compile_inc_code_labels"
  (fun () ->
    `compile_inc cs prog = (cs1,prog1) ==>
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
       prog1)) =
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
       (SND (inline_all cs prog))))`)
  CHEAT_TAC;;

let cache_code_labels_def = cake_define
  `cache_code_labels (cs:(num#bvi_exp) spt) =
     BIGUNION (set_of_list (MAP (bviProps_get_code_labels o SND)
       (sptree_toList cs)))`;;

let lookup_cache_code_labels = cake_theorem "lookup_cache_code_labels"
  (fun () ->
    `sptree_lookup n cs = SOME (arity,body) ==>
     bviProps_get_code_labels body SUBSET cache_code_labels cs`)
  CHEAT_TAC;;

let cache_code_labels_insert = cake_theorem "cache_code_labels_insert"
  (fun () ->
    `!name arity body cs.
       cache_code_labels (sptree_insert name (arity,body) cs)
         SUBSET
         get_code_labels body UNION cache_code_labels cs`)
  CHEAT_TAC;;

let bvi_mk_tick_get_code_labels =
  cake_theorem "bvi_mk_tick_get_code_labels[simp]"
  (fun () ->
    `!n e. get_code_labels (bvi_mk_tick n e) = get_code_labels e`)
  CHEAT_TAC;;

let inline_exp_code_labels = cake_theorem "inline_exp_code_labels"
  (fun () ->
    `(!cs e.
        get_code_labels (inline_exp cs e) SUBSET
          get_code_labels e UNION cache_code_labels cs) /\
     (!cs es.
        BIGUNION (set_of_list (MAP get_code_labels (inline_exps cs
          es))) SUBSET
          BIGUNION (set_of_list (MAP get_code_labels es)) UNION
            cache_code_labels cs)`)
  CHEAT_TAC;;

let inline_all_code_labels = cake_theorem "inline_all_code_labels"
  (fun () ->
    `!cs prog.
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         (SND (inline_all cs prog)))) SUBSET
         BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
           prog)) UNION
         cache_code_labels cs`)
  CHEAT_TAC;;

let compile_prog_code_labels = cake_theorem "compile_prog_code_labels"
  (fun () ->
    `compile_prog prog = (cs1,prog1) ==>
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
       prog1)) SUBSET
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         prog))`)
  CHEAT_TAC;;

let subspt_insert_union_fresh = cake_theorem "subspt_insert_union_fresh"
  (fun () ->
    `!cs old name value.
       subspt cs old /\ ~(name IN domain old) ==>
       subspt (sptree_insert name value cs)
         (sptree_union old (sptree_insert name value LN))`)
  CHEAT_TAC;;

let inline_all_cache_subspt = cake_theorem "inline_all_cache_subspt"
  (fun () ->
    `!prog cs old final_cache out.
       inline_all cs prog = (final_cache,out) /\
       subspt cs old /\
       DISJOINT (set_of_list (MAP FST prog)) (domain old) /\
       ALL_DISTINCT (MAP FST prog) ==>
       subspt final_cache (sptree_union old (fromAList out))`)
  CHEAT_TAC;;

(* [exp_rel c] relates a source expression to its image under the inlining
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

let exp_rel_mono = cake_theorem "exp_rel_mono"
  (fun () ->
    `!c x y. bvi_inlineProof_exp_rel c x y ==> (!c1. subspt c c1 ==>
  bvi_inlineProof_exp_rel c1 x y)`)
  CHEAT_TAC;;

let exp_rel_mono_list = cake_theorem "exp_rel_mono_list"
  (fun () ->
    `LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\ subspt c c1 ==>
  LIST_REL (bvi_inlineProof_exp_rel c1) xs ys`)
  CHEAT_TAC;;

let exp_rel_evaluate_mono = cake_theorem "exp_rel_evaluate_mono[local]"
  (fun () ->
    `(evaluate (es,env,t) = (res,t1) /\ bvi_inlineProof_exp_rel
  (state_code t) x y ==>
        bvi_inlineProof_exp_rel (state_code t1) x y) /\
     (evaluate (es,env,t) = (res,t1) /\ LIST_REL
       (bvi_inlineProof_exp_rel (state_code t)) xs ys ==>
        LIST_REL (bvi_inlineProof_exp_rel (state_code t1)) xs ys)`)
  CHEAT_TAC;;

let exp_rel_refl = cake_theorem "exp_rel_refl[simp]"
  (fun () ->
    `!c x. bvi_inlineProof_exp_rel c x x`)
  CHEAT_TAC;;

let inline_call_none_exp_rel = cake_theorem "inline_call_none_exp_rel"
  (fun () ->
    `subspt cs c /\ LIST_REL (bvi_inlineProof_exp_rel c) es (inline_exps
  cs es) ==>
     bvi_inlineProof_exp_rel c (Call ticks dest es NONE)
       (inline_exp cs (Call ticks dest es NONE))`)
  CHEAT_TAC;;

let inline_exp_rel = cake_theorem "inline_exp_rel"
  (fun () ->
    `subspt cs c ==>
       (!e. bvi_inlineProof_exp_rel c e (inline_exp cs e)) /\
       (!es. LIST_REL (bvi_inlineProof_exp_rel c) es (inline_exps
         cs es))`)
  CHEAT_TAC;;

let evaluate_bvi_mk_tick = cake_theorem "evaluate_bvi_mk_tick"
  (fun () ->
    `!exp env s n.
       evaluate ([bvi_mk_tick n exp],env,s) =
         (if state_clock s < n then
           (Rerr (Rabort Rtimeout_error),state_clock_fupd (K 0)
             s) else evaluate ([exp],env,dec_clock n s))`)
  CHEAT_TAC;;

let bvi_inlineProof_evaluate_expand_env =
  cake_theorem "evaluate_expand_env"
  (fun () ->
    `!xs a s env. ~(FST (evaluate (xs,a,s)) = Rerr (Rabort Rtype_error))
  ==>
       evaluate (xs,a ++ env,s) = evaluate (xs,a,s)`)
  CHEAT_TAC;;

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
  bviSem_state_refs
     t = state_refs s /\ bviSem_state_clock
     t = state_clock s /\ bviSem_state_global
     t = bviSem_state_global s /\ bviSem_state_ffi
     t = state_ffi s /\ bviSem_state_compile_oracle
     t = bvi_inlineProof_in_co (compile_oracle s) /\
     subspt (FST (FST (compile_oracle s 0))) (bviSem_state_code t) /\
       compile
     s = bvi_inlineProof_in_cc (bviSem_state_compile t) /\
     domain (bviSem_state_code t) = domain (state_code s) /\
     (!k arity exp.
        sptree_lookup k (state_code s) = SOME (arity,exp) ==>
        (?exp1. sptree_lookup k (bviSem_state_code t) = SOME
          (arity,exp1) /\
               bvi_inlineProof_exp_rel (bviSem_state_code t) exp
                 exp1))`;;
hol4_overload "in_state_rel" "bvi_inlineProof_in_state_rel";;

let in_state_rel_find_code =
  cake_theorem "in_state_rel_find_code[local]"
  (fun () ->
    `!s t dest vs args exp.
       bvi_inlineProof_in_state_rel s t /\
       find_code dest vs (state_code s) = SOME (args,exp) ==>
       (?exp1. find_code dest vs (state_code t) = SOME (args,exp1)
         /\
         bvi_inlineProof_exp_rel (state_code t) exp exp1)`)
  CHEAT_TAC;;

let inline_all_ALOOKUP = cake_theorem "inline_all_ALOOKUP"
  (fun () ->
    `!prog cs old_target final_cache out k wanted_arity wanted_body.
       inline_all cs prog = (final_cache,out) /\
       subspt cs old_target /\
       DISJOINT (set_of_list (MAP FST prog)) (domain old_target) /\
       ALL_DISTINCT (MAP FST prog) /\
       ALOOKUP prog k = SOME (wanted_arity,wanted_body) ==>
       (?body1.
         ALOOKUP out k = SOME (wanted_arity,body1) /\
         bvi_inlineProof_exp_rel (sptree_union old_target
           (fromAList out)) wanted_body body1)`)
  CHEAT_TAC;;

let do_app_state_swap = cake_theorem "do_app_state_swap[local]"
  (fun () ->
    `~(op = closLang_Install) ==>
         ((do_app op args s = Rval (value,s1) /\
           domain (state_code s) SUBSET domain (state_code t) ==>
           do_app op args
             (state_ffi_fupd (K (state_ffi s))
               (bviSem_state_global_fupd (K (bviSem_state_global s))
               (state_clock_fupd (K (state_clock s)) (state_refs_fupd (K
               (state_refs s)) t)))) =
           Rval
             (value,state_ffi_fupd (K (state_ffi s1))
               (bviSem_state_global_fupd (K (bviSem_state_global s1))
               (state_clock_fupd (K (state_clock s1)) (state_refs_fupd
               (K (state_refs s1))
              t))))) /\
          (do_app op args s = Rerr error /\
           (domain (state_code t) SUBSET domain (state_code s) \/
             ~(error = Rabort Rtype_error)) ==>
           do_app op args
             (state_ffi_fupd (K (state_ffi s))
               (bviSem_state_global_fupd (K (bviSem_state_global s))
               (state_clock_fupd (K (state_clock s)) (state_refs_fupd (K
               (state_refs s)) t)))) =
           Rerr error))`)
  CHEAT_TAC;;

let do_app_state_swap_Rval =
  cake_theorem "do_app_state_swap_Rval[local]"
  (fun () ->
    `!op args (s)
         (source_state)
         (t) value. ~(op = closLang_Install) /\
       do_app op args s = Rval (value,source_state) /\
       domain (bviSem_state_code s) SUBSET domain
         (bviSem_state_code t) ==>
       do_app op args
         (bviSem_state_ffi_fupd (K (bviSem_state_ffi s))
           (bviSem_state_global_fupd (K (bviSem_state_global s))
           (bviSem_state_clock_fupd (K (bviSem_state_clock s))
           (bviSem_state_refs_fupd (K (bviSem_state_refs s)) t)))) =
       Rval
         (value,bviSem_state_ffi_fupd (K (bviSem_state_ffi
           source_state)) (bviSem_state_global_fupd (K
           (bviSem_state_global source_state)) (bviSem_state_clock_fupd
           (K (bviSem_state_clock source_state)) (bviSem_state_refs_fupd
           (K (bviSem_state_refs source_state))
          t))))`)
  CHEAT_TAC;;

let do_app_state_swap_Rerr =
  cake_theorem "do_app_state_swap_Rerr[local]"
  (fun () ->
    `!op args (s)
         (t) error'. ~(op = closLang_Install) /\
       do_app op args s = Rerr error' /\
       (domain (bviSem_state_code t) SUBSET domain
         (bviSem_state_code s) \/ ~(error' = Rabort Rtype_error)) ==>
       do_app op args
         (bviSem_state_ffi_fupd (K (bviSem_state_ffi s))
           (bviSem_state_global_fupd (K (bviSem_state_global s))
           (bviSem_state_clock_fupd (K (bviSem_state_clock s))
           (bviSem_state_refs_fupd (K (bviSem_state_refs s)) t)))) =
           Rerr error'`)
  CHEAT_TAC;;

let inline_all_head_names = cake_theorem "inline_all_head_names[local]"
  (fun () ->
    `inline_all cs ((name,arity,body) :: rest) = (final_cache,out) ==>
     (?tail.
       out = (name,arity,inline_exp cs body) :: tail /\
       MAP FST tail = MAP FST rest)`)
  CHEAT_TAC;;

let inline_all_lookup_union =
  cake_theorem "inline_all_lookup_union[local]"
  (fun () ->
    `inline_all cs prog = (final_cache,out) /\
     subspt cs target /\
     domain target = domain source /\
     (!k arity exp. sptree_lookup k source = SOME (arity,exp) ==>
        (?exp1. sptree_lookup k target = SOME (arity,exp1) /\
               bvi_inlineProof_exp_rel target exp exp1)) /\
     DISJOINT (set_of_list (MAP FST prog)) (domain target) /\
     ALL_DISTINCT (MAP FST prog) ==>
     (!k arity exp.
       sptree_lookup k (sptree_union source (fromAList prog)) =
         SOME (arity,exp) ==>
       (?exp1.
         sptree_lookup k (sptree_union target (fromAList out)) =
           SOME (arity,exp1) /\
         bvi_inlineProof_exp_rel (sptree_union target (fromAList
           out)) exp exp1))`)
  CHEAT_TAC;;

let bvi_inlineProof_do_install_Rerr_type =
  cake_theorem "do_install_Rerr_type[local]"
  (fun () ->
    `!args (s:('c,'ffi)bviSem_state) error'.
       do_install args s = Rerr error' ==>
       error' = Rabort Rtype_error`)
  CHEAT_TAC;;

let in_state_rel_do_install =
  cake_theorem "in_state_rel_do_install[local]"
  (fun () ->
    `bvi_inlineProof_in_state_rel s1 t1 ==>
       (match do_install a s1 with Rerr err ->
           (~(err = Rabort Rtype_error) ==> do_install a t1 = Rerr
             err) | Rval (v,s2) ->
           (?t2. bvi_inlineProof_in_state_rel s2 t2 /\ do_install
             a t1 = Rval (v,t2)))`)
  CHEAT_TAC;;

let in_do_app_lemma = cake_theorem "in_do_app_lemma[local]"
  (fun () ->
    `bvi_inlineProof_in_state_rel s1 t1 ==>
       (match do_app op a s1 with Rerr err ->
           (~(err = Rabort Rtype_error) ==> do_app op a t1 = Rerr
             err) | Rval (v,s2) ->
           (?t2. bvi_inlineProof_in_state_rel s2 t2 /\ do_app op
             a t1 = Rval (v,t2)))`)
  CHEAT_TAC;;

(* Inversion of [exp_rel] on each source constructor. [~inline] is why the
   Call clause has a second disjunct. *)
let exp_rel_inv = cake_theorem "exp_rel_inv[local,simp]"
  (fun () ->
    `(bvi_inlineProof_exp_rel c (Var n:bvi_exp) y <=> y = (Var
  n:bvi_exp)) /\
     (bvi_inlineProof_exp_rel c (Force loc n) y <=> y = Force loc
       n) /\
     (bvi_inlineProof_exp_rel c (If x1 x2 x3) y <=>
        (?y1 y2 y3. y = If y1 y2 y3 /\ bvi_inlineProof_exp_rel c x1
          y1 /\ bvi_inlineProof_exp_rel c x2 y2 /\
          bvi_inlineProof_exp_rel c x3 y3)) /\
     (bvi_inlineProof_exp_rel c (Let xs x) y <=>
        (?ys y1. y = Let ys y1 /\ LIST_REL (bvi_inlineProof_exp_rel
          c) xs ys /\ bvi_inlineProof_exp_rel c x y1)) /\
     (bvi_inlineProof_exp_rel c (Raise x) y <=> (?y1. y = Raise y1
       /\ bvi_inlineProof_exp_rel c x y1)) /\
     (bvi_inlineProof_exp_rel c (Tick x) y <=> (?y1. y = Tick y1 /\
       bvi_inlineProof_exp_rel c x y1)) /\
     (bvi_inlineProof_exp_rel c (Op op xs) y <=>
        (?ys. y = Op op ys /\ LIST_REL (bvi_inlineProof_exp_rel c)
          xs ys)) /\
     (bvi_inlineProof_exp_rel c (bvi_Return xs) y <=>
        (?ys. y = bvi_Return ys /\ LIST_REL
          (bvi_inlineProof_exp_rel c) xs ys)) /\
     (bvi_inlineProof_exp_rel c (bvi_LetCall rets ticks target xs
       x) y <=>
        (?ys y1. y = bvi_LetCall rets ticks target ys y1 /\
          LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\
            bvi_inlineProof_exp_rel c x y1)) /\
     (bvi_inlineProof_exp_rel c (bvi_Call ticks dest xs handler) y
       <=>
        (?ys handler1. y = bvi_Call ticks dest ys handler1 /\
           LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\ OPTREL
             (bvi_inlineProof_exp_rel c) handler handler1) \/
        (?n ys arity body.
           dest = SOME n /\ handler = NONE /\
           y = Let ys (bvi_mk_tick (SUC ticks) body) /\
           LIST_REL (bvi_inlineProof_exp_rel c) xs ys /\
             sptree_lookup n c = SOME (arity,body) /\
           LENGTH ys = arity))`)
  CHEAT_TAC;;

(* The inlined form of a Call evaluates exactly like the Call it replaces:
   the extra environment entries are unreachable, and the two differ on a
   [Ret]-raise only, which the side condition excludes. *)
let evaluate_inlined_call = cake_theorem "evaluate_inlined_call[local]"
  (fun () ->
    `sptree_lookup n (state_code t) = SOME (LENGTH ys,body) /\ ~(FST
  (evaluate ([Call ticks (SOME n) ys NONE],env,t)) =
       Rerr (Rabort Rtype_error)) ==>
     evaluate ([Let ys (bvi_mk_tick (SUC ticks) body)],env,t) =
     evaluate ([Call ticks (SOME n) ys NONE],env,t)`)
  CHEAT_TAC;;

let evaluate_inline = cake_theorem "evaluate_inline"
  (fun () ->
    `!es env s res s1 t es1.
       bvi_inlineProof_in_state_rel s t /\ LIST_REL
         (bvi_inlineProof_exp_rel (state_code t)) es es1 /\
       evaluate (es,env,s) = (res,s1) /\ ~(res = Rerr (Rabort
         Rtype_error)) ==>
       (?t1. evaluate (es1,env,t) = (res,t1) /\
         bvi_inlineProof_in_state_rel s1 t1)`)
  CHEAT_TAC;;

(* HOL4 bvi_inlineProofScript.sml:877-907: a proof *)


(* HOL4 bvi_inlineProofScript.sml:910-912: a proof *)


(* HOL4 bvi_inlineProofScript.sml:915-936: a proof *)


(* HOL4 bvi_inlineProofScript.sml:939-955: a proof *)


(* HOL4 bvi_inlineProofScript.sml:958-972: a proof *)


(* HOL4 bvi_inlineProofScript.sml:975-989: a proof *)


(* HOL4 bvi_inlineProofScript.sml:992-1011: a proof *)


(* HOL4 bvi_inlineProofScript.sml:1014-1028: a proof *)


(* HOL4 bvi_inlineProofScript.sml:1031-1044: a proof *)


(* HOL4 bvi_inlineProofScript.sml:1047-1137: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1139-1198: a proof *)


(* HOL4 bvi_inlineProofScript.sml:1201: a proof *)

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
  <=> bviSem_state_refs
     t = bviSem_state_refs s /\ bviSem_state_clock t =
       bviSem_state_clock s /\ bviSem_state_global t =
       bviSem_state_global s /\ bviSem_state_ffi t = bviSem_state_ffi s
       /\ bviSem_state_code
     t = sptree_map (I ## remove_ticks_exp) (bviSem_state_code s) /\
       bviSem_state_compile_oracle
     t = bvi_inlineProof_remove_ticks_co o
       bviSem_state_compile_oracle s /\ bviSem_state_compile
     s = bvi_inlineProof_remove_ticks_cc (bviSem_state_compile t)`;;

let remove_ticks_exps_NIL = cake_theorem "remove_ticks_exps_NIL[simp]"
  (fun () ->
    `remove_ticks_exps [] = []`)
  CHEAT_TAC;;

let remove_state_rel_find_code_eq =
  cake_theorem "remove_state_rel_find_code_eq[local]"
  (fun () ->
    `!s (t:('c,'ffi)bviSem_state).
       remove_state_rel s t ==>
       (!dest vs.
         find_code dest vs (bviSem_state_code t) =
           OPTION_MAP (I ## remove_ticks_exp) (find_code dest vs
             (state_code s)))`)
  CHEAT_TAC;;

let clock_sub_lt = cake_theorem "clock_sub_lt[local]"
  (fun () ->
    `!x (k:num). ~(x = 0) /\ x <= k ==> x - 1 < k`)
  CHEAT_TAC;;

let evaluate_add_extra_clock =
  cake_theorem "evaluate_add_extra_clock[local]"
  (fun () ->
    `!xs env (s:('c,'ffi)bviSem_state) res s1 extra extra'.
       evaluate (xs,env,bviSem_state_clock_fupd (K (extra +
         bviSem_state_clock s)) s) = (res,s1) /\ ~(res = Rerr (Rabort
         Rtimeout_error)) ==>
       evaluate (xs,env,bviSem_state_clock_fupd (K (extra + extra'
         + bviSem_state_clock s)) s) =
         (res,state_clock_fupd (K (extra' + state_clock s1)) s1)`)
  CHEAT_TAC;;

let clean_prog_CONS = cake_theorem "clean_prog_CONS[local,simp]"
  (fun () ->
    `clean_prog [] = [] /\
     clean_prog (p :: ps) = (I ## I ## remove_ticks_exp) p ::
       clean_prog ps`)
  CHEAT_TAC;;

let clean_prog_simps = cake_theorem "clean_prog_simps[local,simp]"
  (fun () ->
    `MAP FST (clean_prog prog) = MAP FST prog /\
     sptree_map (I ## remove_ticks_exp) (fromAList prog) =
       fromAList (clean_prog prog)`)
  CHEAT_TAC;;

let remove_state_rel_do_install =
  cake_theorem "remove_state_rel_do_install[local]"
  (fun () ->
    `!args (s:('c,'ffi)bviSem_state) t.
       remove_state_rel s t ==>
         (match do_install args s with Rval (value,s1) ->
             (?t1. do_install args t = Rval (value,t1) /\
               remove_state_rel s1 t1) | Rerr err -> do_install args t
               = Rerr err)`)
  CHEAT_TAC;;

let remove_state_rel_do_app =
  cake_theorem "remove_state_rel_do_app[local]"
  (fun () ->
    `!op args (s:('c,'ffi)bviSem_state) t.
       remove_state_rel s t ==>
         (match do_app op args s with Rval (value,s1) ->
             (?t1. do_app op args t = Rval (value,t1) /\
               remove_state_rel s1 t1) | Rerr err -> do_app op args t
               = Rerr err)`)
  CHEAT_TAC;;

let evaluate_remove_ticks_mutual =
  cake_theorem "evaluate_remove_ticks_mutual[local]"
  (fun () ->
    `!k.
       (!e env (t:('c,'ffi)bviSem_state) s res t1.
          remove_state_rel s t /\ bviSem_state_clock t <= k /\
          evaluate ([remove_ticks_exp e],env,t) = (res,t1) ==>
          (?extra s1.
            evaluate ([e],env,state_clock_fupd (K (state_clock s +
              extra)) s) =
              (res,s1) /\ remove_state_rel s1 t1)) /\
       (!es env (t:('c,'ffi)bviSem_state) s res t1.
          remove_state_rel s t /\ bviSem_state_clock t <= k /\
          evaluate (remove_ticks_exps es,env,t) = (res,t1) ==>
          (?extra s1.
            evaluate (es,env,state_clock_fupd (K (state_clock s +
              extra)) s) =
              (res,s1) /\ remove_state_rel s1 t1))`)
  CHEAT_TAC;;

(* HOL4 bvi_inlineProofScript.sml:1362-1366: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1368-1394: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1396-1418: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1420-1432: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1434-1443: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1445-1523: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1525-1552: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1554-1580: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1582-1655: a proof *)


(* HOL4 bvi_inlineProofScript.sml:1658-1671: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1673-1677: a proof *)

(* HOL4 bvi_inlineProofScript.sml:1679-1715: a proof *)


(* HOL4 bvi_inlineProofScript.sml:1718: a proof *)

let evaluate_remove_ticks = cake_theorem "evaluate_remove_ticks"
  (fun () ->
    `!k es env (t:('c,'ffi)bviSem_state) s res t1.
       remove_state_rel s t /\ bviSem_state_clock t = k /\
       evaluate (remove_ticks_exps es,env,t) = (res,t1) ==>
       (?extra s1.
         evaluate (es,env,state_clock_fupd (K (state_clock s +
           extra)) s) =
           (res,s1) /\ remove_state_rel s1 t1)`)
  CHEAT_TAC;;

let state_cc_compile_inc_eq = cake_theorem "state_cc_compile_inc_eq"
  (fun () ->
    `state_cc compile_inc cc = state_cc inline_all
  (bvi_inlineProof_remove_ticks_cc cc)`)
  CHEAT_TAC;;

let state_co_compile_inc_eq = cake_theorem "state_co_compile_inc_eq"
  (fun () ->
    `state_co compile_inc co = bvi_inlineProof_remove_ticks_co o
  state_co inline_all co`)
  CHEAT_TAC;;

let in_cc_eq_state_cc = cake_theorem "in_cc_eq_state_cc[local]"
  (fun () ->
    `bvi_inlineProof_in_cc cc = state_cc inline_all cc`)
  CHEAT_TAC;;

let in_co_eq_state_co = cake_theorem "in_co_eq_state_co[local]"
  (fun () ->
    `bvi_inlineProof_in_co co = state_co inline_all co`)
  CHEAT_TAC;;

let evaluate_add_clock_io_events_mono =
  cake_theorem "evaluate_add_clock_io_events_mono[local]"
  (fun () ->
    `!exps env (s:('c,'ffi)bviSem_state) k extra. ffi_state_io_events
  (state_ffi
       (SND (evaluate (exps,env,bviSem_state_clock_fupd (K k) s))))
         <<= ffi_state_io_events (state_ffi
       (SND (evaluate (exps,env,bviSem_state_clock_fupd (K (k +
         extra)) s))))`)
  CHEAT_TAC;;

let inline_initial_state_rel =
  cake_theorem "inline_initial_state_rel[local]"
  (fun () ->
    `!prog cs1 prog1 co ffi cc clk.
     inline_all LN prog = (cs1,prog1) /\
     FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) ==>
     bvi_inlineProof_in_state_rel
       (initial_state ffi (fromAList prog) co (state_cc inline_all
         cc) clk)
       (initial_state ffi (fromAList prog1) (state_co inline_all
         co) cc clk)`)
  CHEAT_TAC;;

let evaluate_inline_compile =
  cake_theorem "evaluate_inline_compile[local]"
  (fun () ->
    `!prog cs1 prog1 co ffi cc k start' r s.
     inline_all LN prog = (cs1,prog1) /\
     FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) /\
     evaluate ([Call 0 (SOME start') [] NONE],[],
       initial_state ffi (fromAList prog) co (state_cc inline_all
         cc) k) =
         (r,s) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     (?s2.
       evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi (fromAList prog1) (state_co inline_all
           co) cc k) =
           (r,s2) /\
       bvi_inlineProof_in_state_rel s s2)`)
  CHEAT_TAC;;

let evaluate_remove_ticks_compile =
  cake_theorem "evaluate_remove_ticks_compile[local]"
  (fun () ->
    `!prog co ffi cc k start' r s.
     evaluate ([Call 0 (SOME start') [] NONE],[],
       initial_state ffi (fromAList (clean_prog prog))
         (bvi_inlineProof_remove_ticks_co o co) cc k) = (r,s) ==>
     (?ck s2.
       evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi (fromAList prog) co
           (bvi_inlineProof_remove_ticks_cc cc) (k + ck)) =
           (r,s2) /\ state_ffi
       s2 = state_ffi s)`)
  CHEAT_TAC;;

let semantics_not_Fail_cond =
  cake_theorem "semantics_not_Fail_cond[local]"
  (fun () ->
    `!ffi code co cc start'. ~(semantics ffi code co cc start' =
  ffi_Fail) ==>
       ~(?j e. FST (evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi code co cc j)) = Rerr e /\ ~(e =
           Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error
           f))))`)
  CHEAT_TAC;;

let semantics_error_cases = cake_theorem "semantics_error_cases[local]"
  (fun () ->
    `!ffi code co cc start'. ~(semantics ffi code co cc start' =
  ffi_Fail) ==>
       (!j e t. evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi code co cc j) = (Rerr e,t) ==>
         e = Rabort Rtimeout_error \/ (?f. e = Rabort (Rffi_error
           f)))`)
  CHEAT_TAC;;

let semantics_terminate_unique =
  cake_theorem "semantics_terminate_unique[local]"
  (fun () ->
    `!ffi code co cc start' k1 r1 t1 k2 r2 t2.
       evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi code co cc k1) = (r1,t1) /\
       evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi code co cc k2) = (r2,t2) /\ ~(r1 = Rerr
           (Rabort Rtimeout_error)) /\ ~(r2 = Rerr (Rabort
           Rtimeout_error)) ==>
       r1 = r2 /\ state_ffi t1 = state_ffi t2`)
  CHEAT_TAC;;

let semantics_no_type_error =
  cake_theorem "semantics_no_type_error[local]"
  (fun () ->
    `!ffi code co cc start'. ~(semantics ffi code co cc start' =
  ffi_Fail) ==>
       (!j. ~(FST (evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi code co cc j)) = Rerr (Rabort
           Rtype_error)))`)
  CHEAT_TAC;;

let evaluate_compile_prog = cake_theorem "evaluate_compile_prog[local]"
  (fun () ->
    `!prog cs1 prog1 co ffi cc k start' r s.
     compile_prog prog = (cs1,prog1) /\
     FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) /\
     (!j. ~(FST (evaluate ([Call 0 (SOME start') [] NONE],[],
            initial_state ffi (fromAList prog) co
              (state_cc compile_inc cc) j)) = Rerr (Rabort
                Rtype_error))) /\
     evaluate ([Call 0 (SOME start') [] NONE],[],
       initial_state ffi (fromAList prog1) (state_co compile_inc
         co) cc k) =
         (r,s) ==>
     (?ck s2.
       evaluate ([Call 0 (SOME start') [] NONE],[],
         initial_state ffi (fromAList prog) co
           (state_cc compile_inc cc) (k + ck)) = (r,s2) /\
             state_ffi
       s2 = state_ffi s)`)
  CHEAT_TAC;;

let compile_prog_semantics = cake_theorem "compile_prog_semantics"
  (fun () ->
    `compile_prog prog = (cs1,prog1) /\
     FST (FST (co 0)) = cs1 /\
     ALL_DISTINCT (MAP FST prog) ==> ~(semantics ffi (fromAList
       prog) co (state_cc compile_inc cc) start = ffi_Fail) ==>
     semantics ffi (fromAList prog1) (state_co compile_inc co) cc
       start =
     semantics ffi (fromAList prog) co (state_cc compile_inc cc)
       start`)
  CHEAT_TAC;;

cake_hide [];;
