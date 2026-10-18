(* ======================================================== *)
(*  bvi_to_data: ported from HOL4's
    compiler/backend/bvi_to_dataScript.sml  *)
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
needs "lib/comparison.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* compilation from BVI to dataLang *)

let iAssign_def = cake_define
  `iAssign n1 op vs live env =
     (if op_requires_names op then
       let xs = SOME (list_to_num_set (vs ++ live ++ env)) in
         if op = closLang_IntOp Greater then
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
                (dataLang_MakeSpace k (list_to_num_set (vs ++ live ++
                env)))
                  (dataLang_Assign n1 op vs NONE))`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let compile_def = cake_define_list_cheat CHEAT_TAC
  [`bvi_to_data_compile (n:num) (env:num list) tail live [] =
        (dataLang_Skip,([]:num list),n)`;
   `bvi_to_data_compile (n:num) (env:num list) tail live (x :: y :: xs)
  =
         (let (c1,v1,n1) = bvi_to_data_compile n env F live [x] in
         let (c2,vs,n2) = bvi_to_data_compile n1 env F (HD v1 ::
           live) (y :: xs) in
           (dataLang_Seq c1 c2,HD v1 :: vs,n2))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Var
  v):bvi_exp] =
         (let var = any_el v env 0 in
         if tail then (Return [var],[n],n + 1) else
           (dataLang_Skip,[var],MAX n (var + 1)))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(If x1 x2
  x3:bvi_exp)] =
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
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Let xs
  x2:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let (c2,v2,n2) = bvi_to_data_compile n1 (vs ++ env) tail
           live [x2] in
           (dataLang_Seq c1 c2,v2,n2))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Raise
  x1:bvi_exp)] =
         (let (c1,v1,n1) = bvi_to_data_compile n env F live [x1] in
           (dataLang_Seq c1 (dataLang_Raise (HD v1)),v1,n1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Return
  xs:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
           (dataLang_Seq c1 (dataLang_Return vs),[n1],n1 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Op op
  xs:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let c2 = dataLang_Seq c1 (iAssign n1 op (REVERSE vs) live
           env) in
           ((if tail then dataLang_Seq c2 (dataLang_Return [n1])
             else c2),[n1],n1 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Tick
  x1:bvi_exp)] =
         (let (c1,v1,n1) = bvi_to_data_compile n env tail live [x1]
           in
           (dataLang_Seq dataLang_Tick c1,v1,n1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Force loc
  v:bvi_exp)] =
         (let var = any_el v env 0 in
         let ret = (if tail then NONE else SOME (n,list_to_num_set
           (live ++ env))) in
           (Force ret loc var,[n],MAX (n + 1) (var + 1)))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Call ticks
  dest xs NONE:bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let ret = (if tail then NONE else SOME
           ([n1],list_to_num_set (live ++ env))) in
           (dataLang_Seq c1 (mk_ticks ticks (Call ret dest vs
             NONE)),[n1],n1 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [(Call ticks
  dest xs (SOME handler):bvi_exp)] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
         let (c2,v,n2) = bvi_to_data_compile (n1 + 1) (n1 :: env) F
           live [handler] in
         let ret = SOME ([n2],list_to_num_set (live ++ env)) in
         let c3 = (if tail then Return [n2] else dataLang_Skip) in
           (dataLang_Seq c1 (mk_ticks ticks (dataLang_Seq
             (dataLang_Call ret dest vs (SOME (n1,dataLang_Seq c2
             (dataLang_Move n2 (HD v))))) c3)),[n2],n2 + 1))`;
   `bvi_to_data_compile (n:num) (env:num list) tail live [bvi_LetCall
  rets ticks dest xs y] =
         (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
           if y = Return (GENLIST Var rets) then
             (dataLang_Seq c1 (mk_ticks ticks (Call NONE (SOME dest)
               vs NONE)),[n1],n1 + 1) else
             let rs = GENLIST (\i. n1 + i) rets in
             let (c2,v,n2) = bvi_to_data_compile (n1 + rets) (rs ++
               env) tail live [y] in
             let ret = (SOME (rs,list_to_num_set (live ++ env))) in
               (dataLang_Seq (dataLang_Seq c1 (mk_ticks ticks
                 (Call ret (SOME dest) vs NONE))) c2,v,n2))`];;
hol4_overload "compile" "bvi_to_data_compile";;

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_to_dataScript.sml:232-237: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let compile_sing_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\x. match x with INL (n,env,t,l,x) -> bvi_exp_size x | INR
     (n,env,l,xs) -> list_size bvi_exp_size xs)`)
  CHEAT_TAC
  [`bvi_to_data_compile_sing (n:num) (env:num list) tail live ((Var
  v):bvi_exp) =
         (let var = any_el v env 0 in
         if tail then (Return [var],n,n + 1) else
           (dataLang_Skip,var,MAX n (var + 1)))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (If x1 x2
  x3:bvi_exp) =
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
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Let xs
  x2:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let (c2,v2,n2) = bvi_to_data_compile_sing n1 (vs ++ env)
           tail live x2 in
           (dataLang_Seq c1 c2,v2,n2))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Raise
  x1:bvi_exp) =
         (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x1
           in
           (dataLang_Seq c1 (dataLang_Raise v1),v1,n1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Return
  xs:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
           (dataLang_Seq c1 (dataLang_Return vs),n1,n1 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Op op
  xs:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let c2 = dataLang_Seq c1 (iAssign n1 op (REVERSE vs) live
           env) in
           ((if tail then dataLang_Seq c2 (dataLang_Return [n1])
             else c2),n1,n1 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Tick
  x1:bvi_exp) =
         (let (c1,v1,n1) = bvi_to_data_compile_sing n env tail live
           x1 in
           (dataLang_Seq dataLang_Tick c1,v1,n1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Force loc
  v:bvi_exp) =
         (let var = any_el v env 0 in
         let ret = (if tail then NONE else SOME (n,list_to_num_set
           (live ++ env))) in
           (Force ret loc var,n,MAX (n + 1) (var + 1)))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Call
  ticks dest xs NONE:bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let ret = (if tail then NONE else SOME
           ([n1],list_to_num_set (live ++ env))) in
           (dataLang_Seq c1 (mk_ticks ticks (Call ret dest vs
             NONE)),n1,n1 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live (Call
  ticks dest xs (SOME handler):bvi_exp) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
         let (c2,v,n2) = bvi_to_data_compile_sing (n1 + 1) (n1 ::
           env) F live handler in
         let ret = SOME ([n2],list_to_num_set (live ++ env)) in
         let c3 = (if tail then Return [n2] else dataLang_Skip) in
           (dataLang_Seq c1 (mk_ticks ticks
              (dataLang_Seq (dataLang_Call ret dest vs (SOME
                (n1,dataLang_Seq c2 (dataLang_Move n2 v)))) c3)),
            n2,n2 + 1))`;
   `bvi_to_data_compile_sing (n:num) (env:num list) tail live
  (bvi_LetCall rets ticks dest xs y) =
         (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
           if y = Return (GENLIST Var rets) then
             (dataLang_Seq c1 (mk_ticks ticks (Call NONE (SOME dest)
               vs NONE)),n1,n1 + 1) else
             let rs = GENLIST (\i. n1 + i) rets in
             let (c2,v,n2) = bvi_to_data_compile_sing (n1 + rets)
               (rs ++ env) tail live y in
             let ret = (SOME (rs,list_to_num_set (live ++ env))) in
               (dataLang_Seq (dataLang_Seq c1 (mk_ticks ticks
                 (Call ret (SOME dest) vs NONE))) c2,v,n2))`;
   `bvi_to_data_compile_list (n:num) (env:num list) live [] =
        (dataLang_Skip,([]:num list),n)`;
   `bvi_to_data_compile_list (n:num) (env:num list) live (x :: xs) =
         (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x
           in
           if NULL xs then (c1,[v1],n1) else
             let (c2,vs,n2) = bvi_to_data_compile_list n1 env (v1 ::
               live) xs in
               (dataLang_Seq c1 c2,v1 :: vs,n2))`];;
hol4_overload "compile_list" "bvi_to_data_compile_list";;
hol4_overload "compile_sing" "bvi_to_data_compile_sing";;

(* combine dataLang optimisations *)

let optimise_def = cake_define
  `bvi_to_data_optimise prog = data_space_compile (simp (FST
  (data_live_compile prog LN)) dataLang_Skip)`;;
hol4_overload "optimise" "bvi_to_data_optimise";;

(* the top-level compiler includes the optimisations, because the
   correctness
   proofs are combined *)

let compile_exp_def = cake_define
  `bvi_to_data_compile_exp arg_count exp =
     bvi_to_data_optimise (FST (compile arg_count (COUNT_LIST
       arg_count) T [] [exp]))`;;
hol4_overload "compile_exp" "bvi_to_data_compile_exp";;

let compile_part_def = cake_define
  `bvi_to_data_compile_part ((name:num),arg_count,exp) =
     (name,arg_count,bvi_to_data_compile_exp arg_count exp)`;;
hol4_overload "compile_part" "bvi_to_data_compile_part";;

let compile_prog_def = cake_define
  `bvi_to_data_compile_prog prog = MAP bvi_to_data_compile_part prog`;;
hol4_overload "compile_prog" "bvi_to_data_compile_prog";;
