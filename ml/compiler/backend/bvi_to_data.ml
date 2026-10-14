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
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;

(* compilation from BVI to dataLang *)

let iAssign_def = cake_define
  `iAssign n1 closLang_op vs live env =
     (if op_requires_names closLang_op then
       let xs = SOME (list_to_num_set (vs ++ live ++ env)) in
         if closLang_op = closLang_IntOp (GREATER) then
           dataLang_Assign n1 (closLang_IntOp (LESS)) (REVERSE vs) xs
             else if closLang_op = closLang_IntOp closLang_GreaterEq
             then
           dataLang_Assign n1 (closLang_IntOp closLang_LessEq)
             (REVERSE vs) xs else
           dataLang_Assign n1 closLang_op vs xs else
       let k = op_space_req closLang_op (LENGTH vs) in
         if k = 0 then
           (if closLang_op = closLang_WordOp (WordTest ast_W8
             (ast_Compare ast_Gt)) then
              dataLang_Assign n1 (closLang_WordOp (WordTest ast_W8
                (ast_Compare ast_Lt))) (REVERSE vs) NONE else if
                closLang_op = closLang_WordOp (WordTest ast_W8
                (ast_Compare ast_Geq)) then
              dataLang_Assign n1 (closLang_WordOp (WordTest ast_W8
                (ast_Compare ast_Leq))) (REVERSE vs) NONE else
              dataLang_Assign n1 closLang_op vs NONE) else
                dataLang_Seq (dataLang_MakeSpace k (list_to_num_set (vs
                ++ live ++ env)))
                  (dataLang_Assign n1 closLang_op vs NONE))`;;

let compile_def = cake_define
  `(bvi_to_data_compile (n:num) (env:num list) tail live [] =
     (dataLang_Skip,([]:num list),n)) /\
   (bvi_to_data_compile n env tail live (x :: y :: xs) =
      (let (c1,v1,n1) = bvi_to_data_compile n env F live [x] in
      let (c2,vs,n2) = bvi_to_data_compile n1 env F (HD v1 :: live)
        (y :: xs) in
        (dataLang_Seq c1 c2,HD v1 :: vs,n2))) /\
   (bvi_to_data_compile n env tail live [(bvi_Var v):bvi_exp] =
      (let var = any_el v env 0 in
      if tail then (dataLang_Return [var],[n],n + 1) else
        (dataLang_Skip,[var],MAX n (var + 1)))) /\
   (bvi_to_data_compile n env tail live [dataLang_If x1 x2 x3] =
      (let (c1,v1,n1) = bvi_to_data_compile n env F live [x1] in
      let (c2,v2,n2) = bvi_to_data_compile n1 env tail live [x2] in
      let (c3,v3,n3) = bvi_to_data_compile n2 env tail live [x3] in
        if tail then
          (dataLang_Seq c1 (dataLang_If (HD v1) c2 c3),[n3],n3 + 1)
            else
          (dataLang_Seq c1 (dataLang_If (HD v1) (dataLang_Seq c2
            (dataLang_Move n3 (HD v2)))
                              (dataLang_Seq c3 (dataLang_Move n3 (HD
                                v3)))),[n3],n3 + 1))) /\
   (bvi_to_data_compile n env tail live [bvi_Let xs x2] =
      (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let (c2,v2,n2) = bvi_to_data_compile n1 (vs ++ env) tail live
        [x2] in
        (dataLang_Seq c1 c2,v2,n2))) /\
   (bvi_to_data_compile n env tail live [dataLang_Raise x1] =
      (let (c1,v1,n1) = bvi_to_data_compile n env F live [x1] in
        (dataLang_Seq c1 (dataLang_Raise (HD v1)),v1,n1))) /\
   (bvi_to_data_compile n env tail live [dataLang_Return xs] =
      (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
        (dataLang_Seq c1 (dataLang_Return vs),[n1],n1 + 1))) /\
   (bvi_to_data_compile n env tail live [bvi_Op closLang_op xs] =
      (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let c2 = dataLang_Seq c1 (iAssign n1 closLang_op (REVERSE vs)
        live env) in
        (if tail then dataLang_Seq c2 (dataLang_Return [n1]) else
          c2,[n1],n1 + 1))) /\
   (bvi_to_data_compile n env tail live [dataLang_Tick x1] =
      (let (c1,v1,n1) = bvi_to_data_compile n env tail live [x1] in
        (dataLang_Seq dataLang_Tick c1,v1,n1))) /\
   (bvi_to_data_compile n env tail live [dataLang_Force loc v] =
      (let var = any_el v env 0 in
      let ret = (if tail then NONE else SOME (n,list_to_num_set (live
        ++ env))) in
        (dataLang_Force ret loc var,[n],MAX (n + 1) (var + 1)))) /\
   (bvi_to_data_compile n env tail live [dataLang_Call ticks dest xs
     NONE] =
      (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let ret = (if tail then NONE else SOME ([n1],list_to_num_set
        (live ++ env))) in
        (dataLang_Seq c1 (mk_ticks ticks (dataLang_Call ret dest vs
          NONE)),[n1],n1 + 1))) /\
   (bvi_to_data_compile n env tail live [dataLang_Call ticks dest xs
     (SOME handler)] =
      (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let (c2,v,n2) = bvi_to_data_compile (n1 + 1) (n1 :: env) F live
        [handler] in
      let ret = SOME ([n2],list_to_num_set (live ++ env)) in
      let c3 = (if tail then dataLang_Return [n2] else dataLang_Skip)
        in
        (dataLang_Seq c1 (mk_ticks ticks (dataLang_Seq (dataLang_Call
          ret dest vs (SOME (n1,dataLang_Seq c2 (dataLang_Move n2 (HD
          v))))) c3)),[n2],n2 + 1))) /\
   (bvi_to_data_compile n env tail live [bvi_LetCall rets ticks dest
     xs y] =
      (let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
        if y = dataLang_Return (GENLIST bvi_Var rets) then
          (dataLang_Seq c1 (mk_ticks ticks (dataLang_Call NONE (SOME
            dest) vs NONE)),[n1],n1 + 1) else
          let rs = GENLIST (\i. n1 + i) rets in
          let (c2,v,n2) = bvi_to_data_compile (n1 + rets) (rs ++ env)
            tail live [y] in
          let ret = (SOME (rs,list_to_num_set (live ++ env))) in
            (dataLang_Seq (dataLang_Seq c1 (mk_ticks ticks
              (dataLang_Call ret (SOME dest) vs NONE))) c2,v,n2)))`;;

(* HOL4 termination: \\ simp[] *)
let compile_sing_def = cake_define_wf
  `MEASURE (\x. match x with INL (n,env,t,l,x) -> exp_size x | INR
  (n,env,l,xs) -> list_size exp_size xs)`
  `(bvi_to_data_compile_sing n env tail live ((bvi_Var v):bvi_exp) =
      (let var = any_el v env 0 in
      if tail then (dataLang_Return [var],n,n + 1) else
        (dataLang_Skip,var,MAX n (var + 1)))) /\
   (bvi_to_data_compile_sing n env tail live (dataLang_If x1 x2 x3) =
      (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x1 in
      let (c2,v2,n2) = bvi_to_data_compile_sing n1 env tail live x2
        in
      let (c3,v3,n3) = bvi_to_data_compile_sing n2 env tail live x3
        in
        if tail then
          (dataLang_Seq c1 (dataLang_If v1 c2 c3),n3,n3 + 1) else
          (dataLang_Seq c1 (dataLang_If v1 (dataLang_Seq c2
            (dataLang_Move n3 v2))
                            (dataLang_Seq c3 (dataLang_Move n3
                              v3))),n3,n3 + 1))) /\
   (bvi_to_data_compile_sing n env tail live (bvi_Let xs x2) =
      (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
      let (c2,v2,n2) = bvi_to_data_compile_sing n1 (vs ++ env) tail
        live x2 in
        (dataLang_Seq c1 c2,v2,n2))) /\
   (bvi_to_data_compile_sing n env tail live (dataLang_Raise x1) =
      (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x1 in
        (dataLang_Seq c1 (dataLang_Raise v1),v1,n1))) /\
   (bvi_to_data_compile_sing n env tail live (dataLang_Return xs) =
      (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
        (dataLang_Seq c1 (dataLang_Return vs),n1,n1 + 1))) /\
   (bvi_to_data_compile_sing n env tail live (bvi_Op closLang_op xs)
     =
      (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
      let c2 = dataLang_Seq c1 (iAssign n1 closLang_op (REVERSE vs)
        live env) in
        (if tail then dataLang_Seq c2 (dataLang_Return [n1]) else
          c2,n1,n1 + 1))) /\
   (bvi_to_data_compile_sing n env tail live (dataLang_Tick x1) =
      (let (c1,v1,n1) = bvi_to_data_compile_sing n env tail live x1
        in
        (dataLang_Seq dataLang_Tick c1,v1,n1))) /\
   (bvi_to_data_compile_sing n env tail live (dataLang_Force loc v) =
      (let var = any_el v env 0 in
      let ret = (if tail then NONE else SOME (n,list_to_num_set (live
        ++ env))) in
        (dataLang_Force ret loc var,n,MAX (n + 1) (var + 1)))) /\
   (bvi_to_data_compile_sing n env tail live (dataLang_Call ticks
     dest xs NONE) =
      (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
      let ret = (if tail then NONE else SOME ([n1],list_to_num_set
        (live ++ env))) in
        (dataLang_Seq c1 (mk_ticks ticks (dataLang_Call ret dest vs
          NONE)),n1,n1 + 1))) /\
   (bvi_to_data_compile_sing n env tail live (dataLang_Call ticks
     dest xs (SOME handler)) =
      (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
      let (c2,v,n2) = bvi_to_data_compile_sing (n1 + 1) (n1 :: env) F
        live handler in
      let ret = SOME ([n2],list_to_num_set (live ++ env)) in
      let c3 = (if tail then dataLang_Return [n2] else dataLang_Skip)
        in
        (dataLang_Seq c1 (mk_ticks ticks
           (dataLang_Seq (dataLang_Call ret dest vs (SOME
             (n1,dataLang_Seq c2 (dataLang_Move n2 v)))) c3)),
         n2,n2 + 1))) /\
   (bvi_to_data_compile_sing n env tail live (bvi_LetCall rets ticks
     dest xs y) =
      (let (c1,vs,n1) = bvi_to_data_compile_list n env live xs in
        if y = dataLang_Return (GENLIST bvi_Var rets) then
          (dataLang_Seq c1 (mk_ticks ticks (dataLang_Call NONE (SOME
            dest) vs NONE)),n1,n1 + 1) else
          let rs = GENLIST (\i. n1 + i) rets in
          let (c2,v,n2) = bvi_to_data_compile_sing (n1 + rets) (rs ++
            env) tail live y in
          let ret = (SOME (rs,list_to_num_set (live ++ env))) in
            (dataLang_Seq (dataLang_Seq c1 (mk_ticks ticks
              (dataLang_Call ret (SOME dest) vs NONE))) c2,v,n2))) /\
   (bvi_to_data_compile_list (n:num) (env:num list) live [] =
     (dataLang_Skip,([]:num list),n)) /\
   (bvi_to_data_compile_list n env live (x :: xs) =
      (let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x in
        if NULL xs then (c1,[v1],n1) else
          let (c2,vs,n2) = bvi_to_data_compile_list n1 env (v1 ::
            live) xs in
            (dataLang_Seq c1 c2,v1 :: vs,n2)))`;;

(* combine dataLang optimisations *)

let optimise_def = cake_define
  `bvi_to_data_optimise dataLang_prog = data_space_compile (simp (FST
  (data_live_compile dataLang_prog LN)) dataLang_Skip)`;;

(* the top-level compiler includes the optimisations, because the
   correctness
   proofs are combined *)

let compile_exp_def = cake_define
  `bvi_to_data_compile_exp arg_count bvi_exp =
     bvi_to_data_optimise (FST (bvi_to_data_compile arg_count
       (COUNT_LIST arg_count) T [] [bvi_exp]))`;;

let compile_part_def = cake_define
  `bvi_to_data_compile_part ((name:num),arg_count,bvi_exp) =
     (name,arg_count,bvi_to_data_compile_exp arg_count bvi_exp)`;;

let compile_prog_def = cake_define
  `bvi_to_data_compile_prog dataLang_prog = MAP
  bvi_to_data_compile_part dataLang_prog`;;
