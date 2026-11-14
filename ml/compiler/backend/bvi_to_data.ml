(* ======================================================== *)
(*  bvi_to_data: ported from HOL4's
    compiler/backend/bvi_to_dataScript.sml
    A definition theory, with 7 definitions and 10 theorems.  Needed
    by backend.ml, bvi_to_dataProof.ml and
    data_to_word_assignProof.ml.  *)
(* ======================================================== *)

(*
  A compiler phase that turns programs of the functional language BVI
  into the first imperative language of the CakeML compiler: dataLang.
*)

needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/data_space.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvi_to_data"
  ["bvi"; "dataLang"; "data_live"; "data_simp"; "data_space"];;

let _ = do_list hide_constant ["pmatch"];;

(* compilation from BVI to dataLang *)

let op_space_reset_pmatch = prove
 (`!op.
   op_space_reset op =
     (match op with
       closLang_IntOp closLang_Add -> T | closLang_IntOp
         closLang_Sub -> T | closLang_IntOp closLang_Mult -> T |
         closLang_IntOp closLang_Div -> T | closLang_IntOp
         closLang_Mod -> T | closLang_IntOp closLang_Less -> T |
         closLang_IntOp closLang_LessEq -> T | closLang_IntOp
         closLang_Greater -> T | closLang_IntOp closLang_GreaterEq ->
         T | closLang_BlockOp closLang_Equal -> T | closLang_BlockOp
         closLang_ListAppend -> T | closLang_BlockOp
         (closLang_FromList _1) -> T | closLang_BlockOp
         (closLang_ConsExtend _2) -> T | closLang_MemOp
         closLang_RefArray -> T | closLang_MemOp (closLang_RefByte _3)
         -> T | closLang_MemOp (closLang_CopyByte new_flag) ->
         new_flag | closLang_MemOp closLang_ConfigGC -> T |
         closLang_FFI _4 -> T | _5 -> F)`,
  CHEAT_TAC);;

let op_requires_names_eqn = prove
 (`!op. op_requires_names op =
    (op_space_reset op \/ (match op with closLang_FFI n -> T |
      closLang_Install -> T | closLang_MemOp (closLang_CopyByte
      new_flag) -> T | closLang_MemOp closLang_XorByte -> T |
      closLang_MemOp (closLang_StringCmp b cmp) -> T | _6 -> F))`,
  CHEAT_TAC);;

let op_requires_names_pmatch = prove
 (`!op. op_requires_names op =
   (op_space_reset op \/ (match op with closLang_FFI n -> T |
     closLang_Install -> T | closLang_MemOp (closLang_CopyByte
     new_flag) -> T | closLang_MemOp closLang_XorByte -> T |
     closLang_MemOp (closLang_StringCmp b cmp) -> T | _7 -> F))`,
  CHEAT_TAC);;

let iAssign_def = new_definition
  `iAssign n1 op vs live env =
     (if op_requires_names op then
       let xs = SOME (list_to_num_set (APPEND (APPEND vs live) env))
         in
         if op = closLang_IntOp closLang_Greater then
           dataLang_Assign n1 (closLang_IntOp closLang_Less) (REVERSE
             vs) xs else if op = closLang_IntOp closLang_GreaterEq then
           dataLang_Assign n1 (closLang_IntOp closLang_LessEq)
             (REVERSE vs) xs else
           dataLang_Assign n1 op vs xs else
       let k = op_space_req op (LENGTH vs) in
         if k = 0 then
           (if op = closLang_WordOp (WordTest ast_W8 (ast_Compare
             ast_Gt)) then
              dataLang_Assign n1 (closLang_WordOp (WordTest ast_W8
                (ast_Compare ast_Lt))) (REVERSE vs) NONE else if op =
                closLang_WordOp (WordTest ast_W8 (ast_Compare ast_Geq))
                then
              dataLang_Assign n1 (closLang_WordOp (WordTest ast_W8
                (ast_Compare ast_Leq))) (REVERSE vs) NONE else
              dataLang_Assign n1 op vs NONE) else dataLang_Seq
                (dataLang_MakeSpace k (list_to_num_set (APPEND (APPEND
                vs live) env)))
                  (dataLang_Assign n1 op vs NONE))`;;

let _ = do_list hide_constant ["tail"];;

let bvi_to_data_compile_def,bvi_to_data_compile_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`bvi_to_data_compile (n:num) (env:num list) tail live [] =
        (dataLang_Skip,([]:num list),n)`;
   `bvi_to_data_compile (n:num) (env:num list) tail live (CONS x (CONS y
  xs)) =
         (let (c1,v1,n1) = bvi_to_data_compile n env F live [x] in
         let (c2,vs,n2) = bvi_to_data_compile n1 env F (CONS (HD v1)
           live) (CONS y xs) in
           (dataLang_Seq c1 c2,CONS (HD v1) vs,n2))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(bvi_Var
  v):bvi_exp] =
         (let var = any_el v env 0 in
         if tail then (dataLang_Return [var],[n],n + 1) else
           (dataLang_Skip,[var],MAX n (var + 1)))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(dataLang_If
  x1 x2 x3:bvi_exp)] =
         (let (c1,v1,n1) = bvi_to_data_compile n env F live [x1] in
         let (c2,v2,n2) = bvi_to_data_compile n1 env tail live [x2]
           in
         let (c3,v3,n3) = bvi_to_data_compile n2 env tail live [x3]
           in
           if tail then
             (dataLang_Seq c1 (dataLang_If (HD v1) c2 c3),[n3],n3 +
               1) else
             (dataLang_Seq c1 (dataLang_If (HD v1) (dataLang_Seq c2
               (dataLang_Move n3 (HD v2)))
                              (dataLang_Seq c3 (dataLang_Move n3
                                (HD v3)))),[n3],n3 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(bvi_Let xs
  x2:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let (c2,v2,n2) = bvi_to_data_compile n1 (APPEND vs env)
           tail live [x2] in
           (dataLang_Seq c1 c2,v2,n2))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live
  [(dataLang_Raise x1:bvi_exp)] =
         (let (c1,v1,n1) = bvi_to_data_compile n env F live [x1] in
           (dataLang_Seq c1 (dataLang_Raise (HD v1)),v1,n1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live
  [(dataLang_Return xs:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
           (dataLang_Seq c1 (dataLang_Return vs),[n1],n1 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(bvi_Op op
  xs:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let c2 = dataLang_Seq c1 (iAssign n1 op (REVERSE vs) live
           env) in
           ((if tail then dataLang_Seq c2 (dataLang_Return [n1])
             else c2),[n1],n1 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(dataLang_Tick
  x1:bvi_exp)] =
         (let (c1,v1,n1) = bvi_to_data_compile n env tail live [x1]
           in
           (dataLang_Seq dataLang_Tick c1,v1,n1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live
  [(dataLang_Force loc v:bvi_exp)] =
         (let var = any_el v env 0 in
         let ret = (if tail then NONE else SOME (n,list_to_num_set
           (APPEND live env))) in
           (dataLang_Force ret loc var,[n],MAX (n + 1) (var +
             1)))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(dataLang_Call
  ticks dest xs NONE:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let ret = (if tail then NONE else SOME
           ([n1],list_to_num_set (APPEND live env))) in
           (dataLang_Seq c1 (mk_ticks ticks (dataLang_Call ret
             dest vs NONE)),[n1],n1 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(dataLang_Call
  ticks dest xs (SOME handler):bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let (c2,v,n2) = bvi_to_data_compile (n1 + 1) (CONS n1 env)
           F live [handler] in
         let ret = SOME ([n2],list_to_num_set (APPEND live env)) in
         let c3 = (if tail then dataLang_Return [n2] else
           dataLang_Skip) in
           (dataLang_Seq c1 (mk_ticks ticks (dataLang_Seq
             (dataLang_Call ret dest vs (SOME (n1,dataLang_Seq c2
             (dataLang_Move n2 (HD v))))) c3)),[n2],n2 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [bvi_LetCall
  rets ticks dest xs y] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
           if y = dataLang_Return (list_of_seq bvi_Var rets) then
             (
              // tailcall
              dataLang_Seq c1 (mk_ticks ticks (dataLang_Call NONE
                (SOME dest) vs NONE)),[n1],n1 + 1) else
             // non-tailcall
             let rs = list_of_seq (\i. n1 + i) rets in
             let (c2,v,n2) = bvi_to_data_compile (n1 + rets) (APPEND
               rs env) tail live [y] in
             let ret = (SOME (rs,list_to_num_set (APPEND live env)))
               in
               (dataLang_Seq (dataLang_Seq c1 (mk_ticks ticks
                 (dataLang_Call ret (SOME dest) vs NONE)))
                 c2,v,n2))`];;

let compile_sing_def,compile_sing_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`bvi_to_data_compile_sing (n:num) (env:num list) tail live ((bvi_Var
  v):bvi_exp) =
         (let var = any_el v env 0 in
         if tail then (dataLang_Return [var],n,n + 1) else
           (dataLang_Skip,var,MAX n (var + 1)))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (dataLang_If x1 x2 x3:bvi_exp) =
         (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x1
           in
         let (c2,v2,n2) = bvi_to_data_compile_sing n1 env tail live
           x2 in
         let (c3,v3,n3) = bvi_to_data_compile_sing n2 env tail live
           x3 in
           if tail then
             (dataLang_Seq c1 (dataLang_If v1 c2 c3),n3,n3 + 1) else
             (dataLang_Seq c1 (dataLang_If v1 (dataLang_Seq c2
               (dataLang_Move n3 v2))
                              (dataLang_Seq c3 (dataLang_Move n3
                                v3))),n3,n3 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (bvi_Let
  xs x2:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let (c2,v2,n2) = bvi_to_data_compile_sing n1 (APPEND vs
           env) tail live x2 in
           (dataLang_Seq c1 c2,v2,n2))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (dataLang_Raise x1:bvi_exp) =
         (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x1
           in
           (dataLang_Seq c1 (dataLang_Raise v1),v1,n1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (dataLang_Return xs:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
           (dataLang_Seq c1 (dataLang_Return vs),n1,n1 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (bvi_Op op
  xs:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let c2 = dataLang_Seq c1 (iAssign n1 op (REVERSE vs) live
           env) in
           ((if tail then dataLang_Seq c2 (dataLang_Return [n1])
             else c2),n1,n1 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (dataLang_Tick x1:bvi_exp) =
         (let (c1,v1,n1) = bvi_to_data_compile_sing n env tail live
           x1 in
           (dataLang_Seq dataLang_Tick c1,v1,n1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (dataLang_Force loc v:bvi_exp) =
         (let var = any_el v env 0 in
         let ret = (if tail then NONE else SOME (n,list_to_num_set
           (APPEND live env))) in
           (dataLang_Force ret loc var,n,MAX (n + 1) (var + 1)))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (dataLang_Call ticks dest xs NONE:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let ret = (if tail then NONE else SOME
           ([n1],list_to_num_set (APPEND live env))) in
           (dataLang_Seq c1 (mk_ticks ticks (dataLang_Call ret
             dest vs NONE)),n1,n1 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (dataLang_Call ticks dest xs (SOME handler):bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let (c2,v,n2) = bvi_to_data_compile_sing (n1 + 1) (CONS n1
           env) F live handler in
         let ret = SOME ([n2],list_to_num_set (APPEND live env)) in
         let c3 = (if tail then dataLang_Return [n2] else
           dataLang_Skip) in
           (dataLang_Seq c1 (mk_ticks ticks
              (dataLang_Seq (dataLang_Call ret dest vs (SOME
                (n1,dataLang_Seq c2 (dataLang_Move n2 v)))) c3)),
            n2,n2 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (bvi_LetCall rets ticks dest xs y) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
           if y = dataLang_Return (list_of_seq bvi_Var rets) then
             (
              // tailcall
              dataLang_Seq c1 (mk_ticks ticks (dataLang_Call NONE
                (SOME dest) vs NONE)),n1,n1 + 1) else
             // non-tailcall
             let rs = list_of_seq (\i. n1 + i) rets in
             let (c2,v,n2) = bvi_to_data_compile_sing (n1 + rets)
               (APPEND rs env) tail live y in
             let ret = (SOME (rs,list_to_num_set (APPEND live env)))
               in
               (dataLang_Seq (dataLang_Seq c1 (mk_ticks ticks
                 (dataLang_Call ret (SOME dest) vs NONE))) c2,v,n2))`;
   `bvi_to_data_compile_list (n:num) (env:num list) live [] =
        (dataLang_Skip,([]:num list),n)`;
   `bvi_to_data_compile_list (n:num) (env:num list) live (CONS x xs) =
         (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x
           in
           if NULL xs then (c1,[v1],n1) else
             let (c2,vs,n2) = bvi_to_data_compile_list n1 env (CONS
               v1 live) xs in
               (dataLang_Seq c1 c2,CONS v1 vs,n2))`];;

let compile_sing_eq = prove
 (`(!n env t l x c1 v1 n1.
      bvi_to_data_compile_sing n env t l x = (c1,v1,n1) ==>
      bvi_to_data_compile n env t l [x] = (c1,[v1],n1)) /\
   (!n env l xs.
      bvi_to_data_compile_list n env l xs =
      bvi_to_data_compile n env F l xs)`,
  CHEAT_TAC);;

(* [local] *)
let compile_LESS_EQ_lemma = prove
 (`!n env tail live xs.
       n <= SND (SND (bvi_to_data_compile n env tail live xs))`,
  CHEAT_TAC);;

let compile_LESS_EQ = prove
 (`!n env tail live xs c vs new_var.
      (bvi_to_data_compile n env tail live xs = (c,vs,new_var)) ==>
        n <= new_var`,
  (REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL compile_LESS_EQ_lemma) THEN
   ASM_REWRITE_TAC[]));;

(* [local] *)
let compile_LENGTH_lemma = prove
 (`!n env tail live xs.
       (LENGTH (FST (SND (bvi_to_data_compile n env tail live xs)))
         = LENGTH xs)`,
  CHEAT_TAC);;

let compile_LENGTH = prove
 (`!n env tail live xs c vs new_var.
      (bvi_to_data_compile n env tail live xs = (c,vs,new_var)) ==>
        (LENGTH vs = LENGTH xs)`,
  (REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL compile_LENGTH_lemma) THEN
   ASM_REWRITE_TAC[]));;

let compile_SING_IMP = prove
 (`(bvi_to_data_compile n env tail live [x] = (c,vs,new_var)) ==> (?t.
  vs = [t])`,
  (DISCH_THEN (MP_TAC o MATCH_MP compile_LENGTH) THEN
   REWRITE_TAC[LENGTH; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
     MESON_TAC[]));;

(* combine dataLang optimisations *)

let optimise_def = new_definition
  `bvi_to_data_optimise prog = data_space_compile (simp (FST
  (data_live_compile prog LN)) dataLang_Skip)`;;

(* the top-level compiler includes the optimisations, because the correctness
   proofs are combined *)

let compile_exp_def = new_definition
  `bvi_to_data_compile_exp arg_count exp =
     bvi_to_data_optimise (FST (bvi_to_data_compile arg_count
       (COUNT_LIST arg_count) T [] [exp]))`;;

let compile_part_def = new_definition
  `bvi_to_data_compile_part ((name:num),arg_count,exp) =
     (name,arg_count,bvi_to_data_compile_exp arg_count exp)`;;

let compile_prog_def = new_definition
  `bvi_to_data_compile_prog prog = MAP bvi_to_data_compile_part prog`;;

let compile_exp_eq = prove
 (`bvi_to_data_compile_exp arg_count exp =
     bvi_to_data_optimise (FST (bvi_to_data_compile_sing arg_count
       (COUNT_LIST arg_count) T [] exp))`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch";
   "tail"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
