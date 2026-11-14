(* ======================================================== *)
(*  bvl_inlineProof: ported from HOL4's
    compiler/backend/proofs/bvl_inlineProofScript.sml
    A proof theory about bvl_inline.ml, with 13 definitions and 35
    theorems.  Needed by bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_inline
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvl_inlineProof"
  ["backendProps"; "bvlProps"; "bvlSem"; "bvl_handleProof";
   "bvl_inline"];;

(* removal of ticks *)

let bvl_inlineProof_state_rel_def = new_definition
  `bvl_inlineProof_state_rel (s:('c,'ffi)bvlSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     t = bvlSem_state_compile_oracle_fupd (K ((I ##
       MAP (I ## I ## (\x. HD (remove_ticks [x])))) o
         bvlSem_state_compile_oracle s)) (bvlSem_state_compile_fupd (K
         (bvlSem_state_compile t)) (bvlSem_state_code_fupd (K
         (sptree_map (I ## (\x. HD (remove_ticks [x])))
         (bvlSem_state_code s))) s)) /\ bvlSem_state_compile
     s = (\cfg prog. bvlSem_state_compile t cfg
                    (MAP (I ## I ## (\x. HD (remove_ticks [x])))
                      prog))`;;
hol4_overload "state_rel" "bvl_inlineProof_state_rel";;

(* HOL4 bvl_inlineProofScript.sml:25: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:27-28: ML code, not ported *)

(* [local] *)
let do_app_lemma = prove
 (`bvl_inlineProof_state_rel t' r ==>
     (match do_app op (REVERSE a) r with Rerr err -> do_app op
       (REVERSE a) t' = Rerr err | Rval (v,r2) -> (?t2.
       bvl_inlineProof_state_rel t2 r2 /\
                           do_app op (REVERSE a) t' = Rval (v,t2)))`,
  CHEAT_TAC);;

(* evaluate_remove_ticks *)
let bvl_inlineProof_evaluate_remove_ticks = prove
 (`!k xs env s (t:('c,'ffi)bvlSem_state) res s'.
      bvl_inlineProof_state_rel t s /\ state_clock s = k /\
      evaluate (remove_ticks xs,env,s) = (res,s') ==>
      (?ck t'. evaluate (xs,env,bvlSem_state_clock_fupd (K
        (bvlSem_state_clock t + ck)) t) = (res,t') /\
              bvl_inlineProof_state_rel t' s')`,
  CHEAT_TAC);;

(* HOL4 bvl_inlineProofScript.sml:290-294: ML code, not ported *)

let bvl_inlineProof_remove_ticks_cc_def = new_definition
  `bvl_inlineProof_remove_ticks_cc cc =
     (\cfg prog'.
          cc cfg (MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks
            [x]))) prog'))`;;
hol4_overload "remove_ticks_cc" "bvl_inlineProof_remove_ticks_cc";;

let bvl_inlineProof_remove_ticks_co_def = new_definition
  `bvl_inlineProof_remove_ticks_co =
     (I ## MAP (I ## I ## (\x. HD (bvl_inline_remove_ticks [x]))))`;;
hol4_overload "remove_ticks_co" "bvl_inlineProof_remove_ticks_co";;

(* evaluate_compile_prog *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_inlineProof_evaluate_compile_prog = prove
 (cake_as_vars (fun () ->
    `evaluate ([Call 0 (SOME start) []],[],
               initial_state ffi0 (sptree_map
                  (I ## (\x. HD (remove_ticks [x]))) prog)
                  (bvl_inlineProof_remove_ticks_co o co) cc k) =
                    (r,s) ==>
     (?ck (s2:('c,'ffi)bvlSem_state).
       evaluate
        ([Call 0 (SOME start) []],[],
          initial_state ffi0 prog co
            (bvl_inlineProof_remove_ticks_cc cc) (k + ck)) = (r,s2) /\
            bvlSem_state_ffi
       s2 = state_ffi s)`),
  CHEAT_TAC);;

let FST_EQ_LEMMA = prove
 (`FST x = y <=> (?y1. x = (y,y1))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let semantics_remove_ticks = prove
 (cake_as_vars (fun () ->
    `semantics ffi (sptree_map (I ## (\x. HD (remove_ticks [x]))) prog)
  (bvl_inlineProof_remove_ticks_co o co)
                   cc start =
     semantics (ffi:'b ffi_state) prog co
       (bvl_inlineProof_remove_ticks_cc cc) start`),
  CHEAT_TAC);;

let remove_ticks_CONS = prove
 (`!xs x. bvl_inline_remove_ticks (CONS x xs) = CONS (HD (remove_ticks
  [x])) (remove_ticks xs)`,
  CHEAT_TAC);;

(* correctness of tick_inline *)

let bvl_inlineProof_exp_rel = cake_inductive
  `(!cs v. bvl_inlineProof_exp_rel (cs:(num#bvl_exp) spt) [bvl_Var v]
  [bvl_Var v]) /\
   (!cs. bvl_inlineProof_exp_rel cs [] []) /\
   (!cs x x1 xs y y1 ys.
      bvl_inlineProof_exp_rel cs [x] [y] /\
      bvl_inlineProof_exp_rel cs (CONS x1 xs) (CONS y1 ys) ==>
      bvl_inlineProof_exp_rel cs (CONS x (CONS x1 xs)) (CONS y (CONS
        y1 ys))) /\
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

let bvl_inlineProof_in_cc_def = new_definition
  `bvl_inlineProof_in_cc limit' cc =
     (\(cs,cfg) prog.
         let (cs1,prog1) = tick_compile_prog limit' cs prog in
           match cc cfg prog1 with NONE -> NONE | SOME
             (code,data,cfg1) -> SOME (code,data,(cs1,cfg1)))`;;
hol4_overload "in_cc" "bvl_inlineProof_in_cc";;

let bvl_inlineProof_in_state_rel_def = new_definition
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

let subspt_exp_rel = prove
 (`!s1 s2 xs ys. subspt s1 s2 /\ bvl_inlineProof_exp_rel s1 xs ys ==>
  bvl_inlineProof_exp_rel s2 xs ys`,
  CHEAT_TAC);;

let tick_inline_all_acc = prove
 (`!limit' cs t aux.
         tick_inline_all limit' cs t aux =
           (let (cs1,xs) = tick_inline_all limit' cs t [] in
             (cs1,APPEND (REVERSE aux) xs))`,
  CHEAT_TAC);;

let tick_inline_all_names = prove
 (`!limit' cs t aux cs1 xs aux.
     tick_inline_all limit' cs t aux = (cs1,xs) ==> APPEND (MAP FST
       (REVERSE aux)) (MAP FST t) = MAP FST xs`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let tick_compile_prog_IMP = prove
 (cake_as_vars (fun () ->
    `tick_compile_prog limit q0 (CONS (k,prog) t) = (cs1,prog1) ==>
         (?p1 vs. prog1 = CONS (k,p1) vs /\ MAP FST vs = MAP FST
           t)`),
  CHEAT_TAC);;

let subspt_union_lemma = prove
 (`(!x. sptree_lookup x t1 = sptree_lookup x t2) ==>
       subspt x (sptree_union c t1) ==> subspt x (sptree_union c
         t2)`,
  CHEAT_TAC);;

let tick_inline_all_domain = prove
 (`!limit' cs0 in1 cs1 xs.
         tick_inline_all limit' cs0 in1 [] = (cs1,xs) ==>
         domain cs1 SUBSET domain cs0 UNION set_of_list (MAP FST
           xs)`,
  CHEAT_TAC);;

let tick_compile_prog_res_range = prove
 (`!in1 limit' in2 c cs0 cs1.
      tick_compile_prog limit' cs0 in1 = (cs1,in2) /\
      ALL_DISTINCT (MAP FST in1) /\
      subspt cs0 c /\ domain c INTER set_of_list (MAP FST in1) =
        EMPTY ==>
      subspt cs1 (sptree_union c (fromAList in2))`,
  CHEAT_TAC);;

let exp_rel_swap_lemma = prove
 (`!x1 x2 x3. bvl_inlineProof_exp_rel x1 x2 x3 ==>
         (!y1. (!k. sptree_lookup k x1 = sptree_lookup k y1) ==>
           bvl_inlineProof_exp_rel y1 x2 x3)`,
  CHEAT_TAC);;

let exp_rel_swap = prove
 (`!x1 x2 x3 y1.
      (!k. sptree_lookup k x1 = sptree_lookup k y1) ==>
        bvl_inlineProof_exp_rel x1 x2 x3 = bvl_inlineProof_exp_rel y1
        x2 x3`,
  CHEAT_TAC);;

let exp_rel_rw = prove
 (`bvl_inlineProof_exp_rel (sptree_union (sptree_union src_code
  (sptree_insert p1 (p2,p3) LN)) (fromAList in1))
         [exp] [exp2] <=>
       bvl_inlineProof_exp_rel (sptree_union src_code (fromAList
         (CONS (p1,p2,p3) in1))) [exp] [exp2]`,
  CHEAT_TAC);;

let exp_rel_tick_inline = prove
 (`!cs0 xs.
      (!k arity v.
        sptree_lookup k cs0 = SOME (arity,v) ==>
        (?exp.
          sptree_lookup k src_code = SOME (arity,exp) /\
          bvl_inlineProof_exp_rel src_code [exp] [v])) ==>
      bvl_inlineProof_exp_rel src_code xs (tick_inline cs0 xs)`,
  CHEAT_TAC);;

(* [local] *)
let tick_compile_prog_IMP_exp_rel = prove
 (`!limit' cs0 in1 cs1 in2 k arity exp src_code.
       tick_compile_prog limit' cs0 in1 = (cs1,in2) /\
       ALOOKUP in1 k = SOME (arity,exp) /\
       ALL_DISTINCT (MAP FST in1) /\
       (!k arity v.
          sptree_lookup k cs0 = SOME (arity,v) ==>
          (?exp. sptree_lookup k src_code = SOME (arity,exp) /\
                bvl_inlineProof_exp_rel src_code [exp] [v])) /\
       DISJOINT (domain src_code) (set_of_list (MAP FST in1)) /\
       DISJOINT (domain cs0) (set_of_list (MAP FST in1)) ==>
       (?exp2.
         ALOOKUP in2 k = SOME (arity,exp2) /\
         bvl_inlineProof_exp_rel (sptree_union src_code (fromAList
           in1)) [exp] [exp2])`,
  CHEAT_TAC);;

(* in_do_app_lemma[local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_inlineProof_in_do_app_lemma = prove
 (cake_as_vars (fun () ->
    `bvl_inlineProof_in_state_rel limit s1 t1 ==>
       (match do_app op a s1 with Rerr err -> (~(err = Rabort
         Rtype_error) ==> do_app op a t1 = Rerr err) | Rval (v,s2) ->
         (?t2. bvl_inlineProof_in_state_rel limit s2 t2 /\
                             do_app op a t1 = Rval (v,t2)))`),
  CHEAT_TAC);;

(* exp_rel_refl *)
let bvl_inlineProof_exp_rel_refl = prove
 (`!cs xs. bvl_inlineProof_exp_rel cs xs xs`,
  CHEAT_TAC);;

(* evaluate_inline *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_inlineProof_evaluate_inline = prove
 (cake_as_vars (fun () ->
    `!es env s1 res t1 s2 es2.
        bvl_inlineProof_in_state_rel limit s1 t1 /\
          bvl_inlineProof_exp_rel (bvlSem_state_code s1) es es2 /\
        evaluate (es,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
          Rtype_error)) ==>
        (?t2. evaluate (es2,env,t1) = (res,t2) /\
             bvl_inlineProof_in_state_rel limit s2 t2)`),
  CHEAT_TAC);;

let bvl_inlineProof_in_co_def = new_definition
  `bvl_inlineProof_in_co limit' co = (\n.
       (let
          ((cs,cfg),progs) = co n in let
          (cs1,progs) = tick_compile_prog limit' cs progs in
          (cfg,progs)))`;;
hol4_overload "in_co" "bvl_inlineProof_in_co";;

let MAP_FST_tick_inline_all = prove
 (`!limit' cs prog.
      MAP FST (SND (tick_inline_all limit' cs prog [])) = MAP FST
        prog`,
  CHEAT_TAC);;

(* exp_rel_rw *)
let bvl_inlineProof_exp_rel_rw = prove
 (`~(MEM x (MAP FST prog)) ==>
       bvl_inlineProof_exp_rel (sptree_union (sptree_insert x y
         (fromAList prog)) acc) [exp] [exp2] =
       bvl_inlineProof_exp_rel (sptree_union (fromAList prog)
         (sptree_insert x y acc)) [exp] [exp2]`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let lookup_tick_inline_all = prove
 (cake_as_vars (fun () ->
    `!cs0 prog acc.
           (!k arity v.
               sptree_lookup k cs0 = SOME (arity,v) ==>
               (?exp.
                 sptree_lookup k (sptree_union (fromAList prog)
                   acc) = SOME (arity,exp) /\
                 bvl_inlineProof_exp_rel (sptree_union (fromAList
                   prog) acc) [exp] [v])) /\
           DISJOINT (set_of_list (MAP FST prog)) (domain cs0) /\
           DISJOINT (set_of_list (MAP FST prog)) (domain acc) /\
           ALL_DISTINCT (MAP FST prog) ==>
           (!k arity exp.
             sptree_lookup k (fromAList prog) = SOME (arity,exp)
               ==>
             (?exp2.
               sptree_lookup k (fromAList (SND (tick_inline_all
                 limit cs0 prog []))) =
               SOME (arity,exp2) /\ bvl_inlineProof_exp_rel
                 (sptree_union (fromAList prog) acc) [exp] [exp2]))`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let subspt_tick_inline = prove
 (cake_as_vars (fun () ->
    `!prog cs aux.
           subspt cs (fromAList (REVERSE aux)) /\
           ALL (\x. ~(FST x IN domain cs)) prog /\
           ALL_DISTINCT (APPEND (MAP FST prog) (MAP FST aux)) ==>
           subspt (FST (tick_inline_all limit cs prog aux))
                  (fromAList (SND (tick_inline_all limit cs prog
                    aux)))`),
  CHEAT_TAC);;

(* HOL4 bvl_inlineProofScript.sml:1160-1186: a theorem that HOL4
   states as the value of an ML expression: evaluate_initial_state *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let in_evaluate_Call = prove
 (cake_as_vars (fun () ->
    `evaluate
          ([Call 0 (SOME start) []],env,
           initial_state ffi0 (fromAList prog) co
             (bvl_inlineProof_in_cc limit cc1) k) = (res,s2) /\
         FST (FST (co 0)) = FST (tick_compile_prog limit LN prog)
           /\
         ALL_DISTINCT (MAP FST prog) /\ ~(res = Rerr (Rabort
           Rtype_error)) ==>
         (?t2.
           evaluate
             ([Call 0 (SOME start) []],env,
              initial_state ffi0
               (fromAList (SND (tick_compile_prog limit LN prog)))
                 (bvl_inlineProof_in_co limit co) cc1 k) =
             (res,t2) /\ bvlSem_state_ffi s2 = bvlSem_state_ffi
               t2)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let semantics_tick_inline = prove
 (cake_as_vars (fun () ->
    `FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
         ALL_DISTINCT (MAP FST prog) ==> ~(semantics ffi (fromAList
           prog) co (bvl_inlineProof_in_cc limit cc) start = ffi_Fail)
           ==>
         semantics ffi (fromAList (SND (tick_compile_prog limit LN
           prog)))
                       (bvl_inlineProof_in_co limit co) cc start =
         semantics (ffi:'b ffi_state) (fromAList prog) co
           (bvl_inlineProof_in_cc limit cc) start`),
  CHEAT_TAC);;

(* let_op *)

let let_opt_def = new_definition
  `let_opt split_seq cut_size (arity,prog) =
     (arity,compile_any split_seq cut_size arity (let_op_sing
       prog))`;;

let let_state_rel_def = new_definition
  `let_state_rel split_seq cut_size (s:('c,'ffi)bvlSem_state)
  (t:('c,'ffi)bvlSem_state) <=>
     t = bvlSem_state_compile_oracle_fupd (K ((I ##
       MAP (I ## let_opt split_seq cut_size)) o
         bvlSem_state_compile_oracle s)) (bvlSem_state_compile_fupd (K
         (bvlSem_state_compile t)) (bvlSem_state_code_fupd (K
         (sptree_map (let_opt split_seq cut_size) (bvlSem_state_code
         s))) s)) /\ bvlSem_state_compile
     s = (\cfg prog. bvlSem_state_compile t cfg (MAP (I ## let_opt
       split_seq cut_size) prog))`;;

(* HOL4 bvl_inlineProofScript.sml:1432: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1434-1435: ML code, not ported *)

(* [simp] *)
let HD_let_op = prove
 (`[HD (let_op [x:bvl_exp])] = let_op [x]`,
  CHEAT_TAC);;

let let_op_sing_thm = prove
 (`let_op_sing (x:bvl_exp) = HD (let_op [x])`,
  CHEAT_TAC);;

let var_list_IMP_evaluate = prove
 (`!a2 a1 l (xs:bvl_exp list) (s:('a,'b)bvlSem_state).
         var_list (LENGTH a1) l xs /\ LENGTH xs = LENGTH a2 ==>
         evaluate (l,APPEND (APPEND a1 a2) env,s) = (Rval a2,s)`,
  CHEAT_TAC);;

(* var_list_IMP_evaluate *)
let bvl_inlineProof_var_list_IMP_evaluate = prove
 (`var_list 0 l xs /\ LENGTH (xs:bvl_exp list) = LENGTH a ==>
       evaluate (l,APPEND a env,(s:('a,'b)bvlSem_state)) = (Rval
         a,s)`,
  CHEAT_TAC);;

(* LENGTH_let_op *)
let bvl_inlineProof_LENGTH_let_op = prove
 (`!(xs:bvl_exp list). LENGTH (let_op xs) = LENGTH xs`,
  CHEAT_TAC);;

(* do_app_lemma[local] *)
let bvl_inlineProof_do_app_lemma = prove
 (`let_state_rel q4 l4 s1 t1 ==>
     (match do_app op a s1 with Rerr err -> do_app op a t1 = Rerr err
       | Rval (v,s2) -> (?t2. let_state_rel q4 l4 s2 t2 /\
                           do_app op a t1 = Rval (v,t2)))`,
  CHEAT_TAC);;

let evaluate_let_op = prove
 (`!es env s1 res t1 s2.
      let_state_rel q4 l4 s1 t1 /\
      evaluate (es,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
        Rtype_error)) ==>
      (?t2. evaluate (let_op es,env,t1) = (res,t2) /\ let_state_rel
        q4 l4 s2 t2)`,
  CHEAT_TAC);;

let let_op_cc_def = new_definition
  `let_op_cc q4 l4 cc =
      (\cfg prog. cc cfg (MAP (I ## let_opt q4 l4) prog))`;;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let let_evaluate_Call = prove
 (cake_as_vars (fun () ->
    `evaluate ([Call 0 (SOME start) []],[],
                initial_state ffi0 prog co (let_op_cc q4 l4 cc) k)
                  = (r,s) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
      (?(s2:('c,'ffi)bvlSem_state).
        evaluate
         ([Call 0 (SOME start) []],[],
           initial_state ffi0 (sptree_map (let_opt q4 l4) prog)
             ((I ## MAP (I ## let_opt q4 l4)) o co)
             cc k) = (r,s2) /\ bvlSem_state_ffi
        s2 = state_ffi s /\ state_clock s = bvlSem_state_clock
          s2)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let semantics_let_op = prove
 (cake_as_vars (fun () ->
    `~(semantics ffi prog co (let_op_cc q4 l4 cc) start = ffi_Fail) ==>
         semantics ffi (sptree_map (let_opt q4 l4) prog)
                       ((I ## MAP (I ## let_opt q4 l4)) o co) cc
                         start =
         semantics (ffi:'b ffi_state) prog co (let_op_cc q4 l4
           cc) start`),
  CHEAT_TAC);;

(* combined theorems *)

let remove_ticks_mk_tick = prove
 (`!n r. remove_ticks [mk_tick n r] = remove_ticks [r]`,
  CHEAT_TAC);;

let is_small_aux_0 = prove
 (`!(n:num) xs. is_small_aux 0 xs = 0`,
  CHEAT_TAC);;

let is_small_aux_CONS = prove
 (`is_small_aux n (CONS x xs) =
       (if n = 0 then n else
         let n = is_small_aux n [x] in
           if n = 0 then n else is_small_aux n xs)`,
  CHEAT_TAC);;

let is_small_aux_remove_ticks = prove
 (`!limit' d. is_small_aux limit' (remove_ticks d) = is_small_aux
  limit' d`,
  CHEAT_TAC);;

let is_rec_CONS = prove
 (`bvl_inline_is_rec n (CONS x xs) <=> bvl_inline_is_rec n [x] \/
  bvl_inline_is_rec n xs`,
  CHEAT_TAC);;

let is_rec_remove_ticks = prove
 (`!p_1 xs. bvl_inline_is_rec p_1 (remove_ticks xs) =
  bvl_inline_is_rec p_1 xs`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let must_inline_remove_ticks = prove
 (cake_as_vars (fun () ->
    `must_inline p_1 limit (HD (remove_ticks (tick_inline cs [p_2]))) =
         must_inline p_1 limit (HD ((tick_inline cs [p_2])))`),
  CHEAT_TAC);;

let let_opt_remove_def = new_definition
  `let_opt_remove b l (arity,prog) =
     let_opt b l (arity,HD (remove_ticks [prog]))`;;

let map_fromAList_HASH = prove
 (`sptree_map f (fromAList ls) = fromAList (MAP (I ## f) ls)`,
  CHEAT_TAC);;

let map_fromAList = prove
 (`!xs f. sptree_map f (fromAList xs) = fromAList (MAP (I ## f) xs)`,
  CHEAT_TAC);;

(* HOL4 bvl_inlineProofScript.sml:1939-1942: ML code, not ported *)

(* HOL4 bvl_inlineProofScript.sml:1944-1947: ML code, not ported *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let inline_ticks = prove
 (cake_as_vars (fun () ->
    `FST (FST (co 0)) = (FST (tick_compile_prog limit LN prog)) /\
         ALL_DISTINCT (MAP FST prog) ==> ~(semantics ffi (fromAList
           prog) co
           (bvl_inlineProof_in_cc limit
             (bvl_inlineProof_remove_ticks_cc cc)) start = ffi_Fail) ==>
         semantics ffi (fromAList (MAP (I ## I ## (\x. HD
           (remove_ticks [x])))
                              (SND (tick_compile_prog limit LN
                                prog))))
           (bvl_inlineProof_remove_ticks_co o bvl_inlineProof_in_co
             limit co) cc start =
         semantics ffi (fromAList prog) co (bvl_inlineProof_in_cc
           limit (bvl_inlineProof_remove_ticks_cc cc)) start`),
  CHEAT_TAC);;

let comp_lemma = prove
 (`(I ## let_opt q4 l4) o (I ## I ## (\x. HD (remove_ticks [x]))) =
       (I ## let_opt_remove q4 l4)`,
  CHEAT_TAC);;

let bvl_inline_cc_def = new_definition
  `bvl_inline_cc limit' q4 l4 cc =
     (bvl_inlineProof_in_cc limit'
       (bvl_inlineProof_remove_ticks_cc (let_op_cc q4 l4 cc)))`;;

let bvl_inline_co_def = new_definition
  `bvl_inline_co limit' q4 l4 co =
    (\x. (I ## MAP (I ## let_opt q4 l4))
           (bvl_inlineProof_remove_ticks_co (bvl_inlineProof_in_co
             limit' co x)))`;;

let MAP_optimise = prove
 (`!prog.
         MAP (bvl_inline_optimise o1 o2) prog =
         MAP (I ## let_opt o1 o2)
           (MAP (I ## I ## (\x. HD (remove_ticks [x]))) prog)`,
  CHEAT_TAC);;

(* state_cc_compile_inc_eq *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_inlineProof_state_cc_compile_inc_eq = prove
 (cake_as_vars (fun () ->
    `(state_cc (compile_inc limit o1 o2) cc) =
        (bvl_inlineProof_in_cc limit
          (bvl_inlineProof_remove_ticks_cc (let_op_cc o1 o2 cc)))`),
  CHEAT_TAC);;

(* state_co_compile_inc_eq *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_inlineProof_state_co_compile_inc_eq = prove
 (cake_as_vars (fun () ->
    `(state_co (compile_inc limit o1 o2) co) =
        ((I ## MAP (I ## let_opt o1 o2)) o
          bvl_inlineProof_remove_ticks_co o bvl_inlineProof_in_co
          limit co)`),
  CHEAT_TAC);;

(* compile_prog_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let bvl_inlineProof_compile_prog_semantics = prove
 (cake_as_vars (fun () ->
    `compile_prog limit o1 o2 prog = (s1,prog1) /\
      FST (FST (co 0)) = s1 /\
      ALL_DISTINCT (MAP FST prog) ==> ~(semantics ffi (fromAList
        prog) co (state_cc (compile_inc limit o1 o2) cc)
        start = ffi_Fail) ==>
      semantics ffi (fromAList prog1) (state_co (compile_inc limit
        o1 o2) co) cc
        start =
      semantics ffi (fromAList prog) co (state_cc (compile_inc
        limit o1 o2) cc)
        start`),
  CHEAT_TAC);;

let handle_ok_optimise = prove
 (`!prog. handle_ok (MAP (SND o SND o bvl_inline_optimise b i) prog)`,
  CHEAT_TAC);;

let compile_prog_handle_ok = prove
 (`compile_prog l b i prog = (inlines,prog3) ==>
    handle_ok (MAP (SND o SND) prog3)`,
  CHEAT_TAC);;

(* [simp] *)
let MAP_FST_MAP_optimise = prove
 (`MAP FST (MAP (bvl_inline_optimise x y) z) = MAP FST z`,
  CHEAT_TAC);;

let compile_prog_names = prove
 (`compile_prog l b i prog = (inlines,prog3) ==>
    MAP FST prog3 = MAP FST prog`,
  CHEAT_TAC);;

let var_list_code_labels_imp = prove
 (`!n x y. var_list n x y ==> UNIONS (set_of_list (MAP
  bvlProps_get_code_labels x)) = {}`,
  CHEAT_TAC);;

let let_op_code_labels = prove
 (`!x. UNIONS (set_of_list (MAP bvlProps_get_code_labels (let_op x)))
  = UNIONS (set_of_list (MAP bvlProps_get_code_labels x))`,
  CHEAT_TAC);;

(* [simp] *)
let let_op_sing_code_labels = prove
 (`bvlProps_get_code_labels (let_op_sing x) = bvlProps_get_code_labels
  x`,
  CHEAT_TAC);;

let remove_ticks_code_labels = prove
 (`!x.
     UNIONS (set_of_list (MAP bvlProps_get_code_labels (remove_ticks
       x))) =
     UNIONS (set_of_list (MAP bvlProps_get_code_labels x))`,
  CHEAT_TAC);;

let optimise_get_code_labels = prove
 (`!x y z.
     bvlProps_get_code_labels (SND (SND (bvl_inline_optimise x y z)))
       SUBSET
     bvlProps_get_code_labels (SND (SND z))`,
  CHEAT_TAC);;

let tick_inline_code_labels = prove
 (`!cs xs.
     UNIONS (set_of_list (MAP bvlProps_get_code_labels (tick_inline
       cs xs))) SUBSET
     UNIONS (set_of_list (MAP bvlProps_get_code_labels xs)) UNION
     UNIONS (set_of_list (MAP (bvlProps_get_code_labels o SND)
       (toList cs)))`,
  CHEAT_TAC);;

let tick_inline_all_code_labels = prove
 (`!limit' cs xs aux cs1 xs1.
     tick_inline_all limit' cs xs aux = (cs1,xs1) ==>
     UNIONS (set_of_list (MAP (bvlProps_get_code_labels o SND o SND)
       xs1)) SUBSET
     UNIONS (set_of_list (MAP (bvlProps_get_code_labels o SND o SND)
       xs)) UNION
     UNIONS (set_of_list (MAP (bvlProps_get_code_labels o SND o SND)
       aux)) UNION
     UNIONS (set_of_list (MAP (bvlProps_get_code_labels o SND)
       (toList cs)))`,
  CHEAT_TAC);;

let compile_prog_get_code_labels = prove
 (`bvl_inline_compile_prog x y z p = (inlines,q) ==>
   UNIONS (set_of_list (MAP (bvlProps_get_code_labels o SND o SND)
     q)) SUBSET
   UNIONS (set_of_list (MAP (bvlProps_get_code_labels o SND o SND)
     p))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
