(* ======================================================== *)
(*  bvl_handle: ported from HOL4's
    compiler/backend/bvl_handleScript.sml  *)
(* ======================================================== *)

(*
  BVL transformation that introduces a Let into each Handle
  body. This is preparation for BVL --> BVI compilation.  This phase
  also removes Handles in case the body cannot raise an exception.
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/db_vars.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

let can_raise_def = cake_define
  `(can_raise (db_vars_Var v) = F) /\
   (can_raise (bvl_If x1 x2 x3) = (can_raise x1 \/ can_raise x2 \/
     can_raise x3)) /\
   (can_raise (bvl_Let xs x2) = (can_raise x2 \/ can_raise1 xs)) /\
   (can_raise (bvl_Handle x1 x2) = can_raise x2) /\
   (can_raise (bvl_Raise x1) = T) /\
   (can_raise (bvl_Op closLang_op xs) = (closLang_op =
     closLang_ThunkOp ForceThunk \/ can_raise1 xs)) /\
   (can_raise (bvl_Tick x) = can_raise x) /\
   (can_raise (bvl_Force m n) = T) /\
   (can_raise (bvl_Call t dest xs) = T) /\
   (can_raise1 [] = F) /\
   (can_raise1 (x :: xs) = (can_raise x \/ can_raise1 xs))`;;

let dest_handle_Raise_def = cake_define
  `dest_handle_Raise x1 =
      match x1 with
        (bvl_Raise x) -> (if can_raise x then NONE else SOME x)
      | _1 -> NONE`;;

let dest_handle_Let_def = cake_define
  `dest_handle_Let x1 =
      match x1 with
        (bvl_Let xs x) -> (if can_raise1 xs then NONE else SOME
          (xs,x))
      | _2 -> NONE`;;

let dest_handle_If_def = cake_define
  `dest_handle_If x1 =
      match x1 with
        (bvl_If x1 x2 x3) ->
     (if can_raise x1 then NONE else
      if can_raise x2 then (if can_raise x3 then NONE else SOME (INL
        (x1,x2,x3))) else
      if can_raise x3 then (if can_raise x2 then NONE else SOME (INR
        (x1,x2,x3))) else
        NONE)
      | _3 -> NONE`;;

let handle_adj_vars_def = cake_define
  `(handle_adj_vars l d (db_vars_Var v) = db_vars_Var (if v < l then v
  else v + d)) /\
   (handle_adj_vars l d (bvl_If x1 x2 x3) =
      bvl_If (handle_adj_vars l d x1) (handle_adj_vars l d x2)
        (handle_adj_vars l d x3)) /\
   (handle_adj_vars l d (bvl_Let xs x2) =
      bvl_Let (handle_adj_vars1 l d xs) (handle_adj_vars (l + LENGTH
        xs) d x2)) /\
   (handle_adj_vars l d (bvl_Handle x1 x2) =
      bvl_Handle (handle_adj_vars l d x1) (handle_adj_vars (l + 1) d
        x2)) /\
   (handle_adj_vars l d (bvl_Raise x1) = bvl_Raise (handle_adj_vars l
     d x1)) /\
   (handle_adj_vars l d (bvl_Op closLang_op xs) = bvl_Op closLang_op
     (handle_adj_vars1 l d xs)) /\
   (handle_adj_vars l d (bvl_Tick x) = bvl_Tick (handle_adj_vars l d
     x)) /\
   (handle_adj_vars l d (bvl_Force m v) = bvl_Force m (if v < l then
     v else v + d)) /\
   (handle_adj_vars l d (bvl_Call t dest xs) =
      bvl_Call t dest (handle_adj_vars1 l d xs)) /\
   (handle_adj_vars1 l d [] = []) /\
   (handle_adj_vars1 l d (x :: xs) = handle_adj_vars l d x ::
     handle_adj_vars1 l d xs)`;;

let handle_size_def = cake_define
  `(handle_size (db_vars_Var v) = 1) /\
   (handle_size (bvl_If x1 x2 x3) = 1 + handle_size x1 + handle_size
     x2 + handle_size x3) /\
   (handle_size (bvl_Let xs x2) = 1 + handle_size x2 + handle_size1
     xs) /\
   (handle_size (bvl_Handle x1 x2) = 1 + 5 * (handle_size x1 +
     handle_size x2)) /\
   (handle_size (bvl_Raise x1) = 1 + handle_size x1) /\
   (handle_size (bvl_Op closLang_op xs) = 1 + handle_size1 xs) /\
   (handle_size (bvl_Tick x) = 1 + handle_size x) /\
   (handle_size (bvl_Force m n) = 1) /\
   (handle_size (bvl_Call t dest xs) = 1 + handle_size1 xs) /\
   (handle_size1 [] = (1:num)) /\
   (handle_size1 (x :: xs) = 1 + handle_size x + handle_size1 xs)`;;

(* HOL4 termination: \\ rpt conj_tac \\ rpt gen_tac \\ simp_tac
   std_ss [] \\ fs [handle_size_def] \\ rw [] \\ gvs
   [DefnBase.one_line_ify NONE dest_handle_If_def,AllCaseEqs()] \\
   gvs [DefnBase.one_line_ify NONE
   dest_handle_Raise_def,AllCaseEqs()] \\ fs [handle_size_def] \\ rw
   [] \\ fs [dest_handle_Let_def,handle_size_non_zero] *)
let handle_simp_def = cake_define_wf
  `MEASURE (\x. match x with INL a -> handle_size a | INR (INL a) ->
  handle_size1 a | INR (INR (a,b,_4)) -> handle_size a + handle_size b)`
  `(handle_simp (bvl_Handle x1 x2) = make_handle x1 x2 0) /\
   (handle_simp (db_vars_Var v) = db_vars_Var v) /\
   (handle_simp (bvl_If x1 x2 x3) = bvl_If (handle_simp x1)
     (handle_simp x2) (handle_simp x3)) /\
   (handle_simp (bvl_Let xs x2) = bvl_Let (handle_simp_list xs)
     (handle_simp x2)) /\
   (handle_simp (bvl_Raise x1) = bvl_Raise (handle_simp x1)) /\
   (handle_simp (bvl_Op closLang_op xs) = bvl_Op closLang_op
     (handle_simp_list xs)) /\
   (handle_simp (bvl_Tick x) = bvl_Tick (handle_simp x)) /\
   (handle_simp (bvl_Force m n) = bvl_Force m n) /\
   (handle_simp (bvl_Call t dest xs) = bvl_Call t dest
     (handle_simp_list xs)) /\
   (handle_simp_list [] = ([]:bvl_exp list)) /\
   (handle_simp_list (x :: xs) = handle_simp x :: handle_simp_list
     xs) /\
   (make_handle x1 x2 l =
      (match dest_handle_Raise x1 with SOME r -> bvl_Let [r]
        (handle_adj_vars 1 l (handle_simp x2)) | NONE ->
      (match dest_handle_Let x1 with SOME (xs,x) -> bvl_Let
        (handle_simp_list xs) (make_handle x x2 (l + LENGTH xs)) | NONE
        ->
      (match dest_handle_If x1 with SOME (INR (b1,b2,b3)) -> bvl_If
        (handle_simp b1)
                              (handle_simp b2)
                              (make_handle b3 x2 l) | SOME (INL
                                (b1,b2,b3)) -> bvl_If (handle_simp b1)
                              (make_handle b2 x2 l)
                              (handle_simp b3) | NONE ->
                                (bvl_Handle (handle_simp x1)
                                (handle_adj_vars 1 l (handle_simp
                                x2)))))))`;;

let SmartLet_def = cake_define
  `SmartLet xs x = (if NULL xs then x else bvl_Let xs x)`;;

let LetLet_def = cake_define
  `LetLet env_length fvs (body:bvl_exp) =
     (let xs = GENLIST I env_length in
     let zs = FILTER (\n. IS_SOME (sptree_lookup n fvs)) xs in
     let ys = MAPi (\i x. (x,i)) zs in
     let long_list = GENLIST (\n. match ALOOKUP ys n with NONE ->
       bvl_Op (closLang_IntOp (closLang_Const 0)) [] | SOME k ->
       db_vars_Var k) env_length in
       bvl_Let (MAP db_vars_Var zs) (SmartLet long_list body))`;;

let OptionalLetLet_def = cake_define
  `OptionalLetLet e env_size live s (limit:num) (nr:bool) =
     (if s < limit then ([e],live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         ([(bvl_Let [] (LetLet env_size fvs e))],flat_live,0,nr))`;;

let OptionalLetLet_sing_def = cake_define
  `OptionalLetLet_sing e env_size live s (limit:num) (nr:bool) =
     (if s < limit then (e,live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         ((bvl_Let [] (LetLet env_size fvs e)),flat_live,0,nr))`;;

let compile_def = cake_define
  `(bvl_handle_compile l n [] = (([]:bvl_exp list),db_vars_Empty,0,T))
  /\
   (bvl_handle_compile l n (x :: y :: xs) =
      (let (dx,lx,s1,nr1) = bvl_handle_compile l n [x] in
      let (dy,ly,s2,nr2) = bvl_handle_compile l n (y :: xs) in
        (dx ++ dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2)))) /\
   (bvl_handle_compile l n [db_vars_Var v] = (if v < n then
     ([db_vars_Var v],db_vars_Var v,1,T) else ([bvl_Op (closLang_IntOp
     (closLang_Const 0)) []],db_vars_Empty,1,T))) /\
   (bvl_handle_compile l n [bvl_If x1 x2 x3] =
      (let (x1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
      let (x2,l2,s2,nr2) = bvl_handle_compile l n [x2] in
      let (x3,l3,s3,nr3) = bvl_handle_compile l n [x3] in
        OptionalLetLet (bvl_If (HD x1) (HD x2) (HD x3)) n
          (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
          (nr1 /\ nr2 /\ nr3))) /\
   (bvl_handle_compile l n [bvl_Let xs x2] =
      (if NULL xs then
        bvl_handle_compile l n [x2] else
        let k = LENGTH xs in
        let (xs,l1,s1,nr1) = bvl_handle_compile l n xs in
        let (x2,l2,s2,nr2) = bvl_handle_compile l (n + k) [x2] in
          OptionalLetLet (bvl_Let xs (HD x2)) n
            (mk_Union l1 (db_vars_Shift k l2)) (s1 + s2 + 1) l (nr1
              /\ nr2))) /\
   (bvl_handle_compile l n [bvl_Handle x1 x2] =
      (let (y1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
        if nr1 then (y1,l1,s1,T) else
          let (y2,l2,s2,nr2) = bvl_handle_compile l (n + 1) [x2] in
            ([bvl_Handle (LetLet n (db_to_set l1) (HD y1)) (HD y2)],
             mk_Union l1 (db_vars_Shift 1 l2),
             s2,nr2))) /\
   (bvl_handle_compile l n [bvl_Raise x1] =
      (let (dx,lx,s1,nr1) = bvl_handle_compile l n [x1] in
        OptionalLetLet (bvl_Raise (HD dx)) n lx (s1 + 1) l F)) /\
   (bvl_handle_compile l n [bvl_Op closLang_op xs] =
      (let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
        if closLang_op = closLang_ThunkOp ForceThunk then
          ([bvl_Op closLang_op ys],lx,s1 + 1,F) else
          OptionalLetLet (bvl_Op closLang_op ys) n lx (s1 + 1) l
            nr1)) /\
   (bvl_handle_compile l n [bvl_Tick x] =
      (let (y,lx,s1,nr1) = bvl_handle_compile l n [x] in
        ([bvl_Tick (HD y)],lx,s1,nr1))) /\
   (bvl_handle_compile l n [bvl_Force m v] = (if v < n then
     ([bvl_Force m v],db_vars_Var v,1,F) else ([bvl_Op (closLang_IntOp
     (closLang_Const 0)) []],db_vars_Empty,1,T))) /\
   (bvl_handle_compile l n [bvl_Call t dest xs] =
      (let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
        OptionalLetLet (bvl_Call t dest ys) n lx (s1 + 1) l F))`;;

(* HOL4 ML code, not ported:
val compile_ind = theorem"compile_ind";
*)

let compile_sing_def = cake_define
  `(bvl_handle_compile_sing l n (db_vars_Var v) = (if v < n then
  (db_vars_Var v,db_vars_Var v,1,T) else (bvl_Op (closLang_IntOp
  (closLang_Const 0)) [],db_vars_Empty,1,T))) /\
   (bvl_handle_compile_sing l n (bvl_If x1 x2 x3) =
      (let (x1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
      let (x2,l2,s2,nr2) = bvl_handle_compile_sing l n x2 in
      let (x3,l3,s3,nr3) = bvl_handle_compile_sing l n x3 in
        OptionalLetLet_sing (bvl_If x1 x2 x3) n
          (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
          (nr1 /\ nr2 /\ nr3))) /\
   (bvl_handle_compile_sing l n (bvl_Let xs x2) =
      (if NULL xs then
        bvl_handle_compile_sing l n x2 else
        let k = LENGTH xs in
        let (xs,l1,s1,nr1) = bvl_handle_compile_list l n xs in
        let (x2,l2,s2,nr2) = bvl_handle_compile_sing l (n + k) x2 in
          OptionalLetLet_sing (bvl_Let xs x2) n
            (mk_Union l1 (db_vars_Shift k l2)) (s1 + s2 + 1) l (nr1
              /\ nr2))) /\
   (bvl_handle_compile_sing l n (bvl_Handle x1 x2) =
      (let (y1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
        if nr1 then (y1,l1,s1,T) else
          let (y2,l2,s2,nr2) = bvl_handle_compile_sing l (n + 1) x2
            in
            (bvl_Handle (LetLet n (db_to_set l1) y1) y2,
             mk_Union l1 (db_vars_Shift 1 l2),
             s2,nr2))) /\
   (bvl_handle_compile_sing l n (bvl_Raise x1) =
      (let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x1 in
        OptionalLetLet_sing (bvl_Raise dx) n lx (s1 + 1) l F)) /\
   (bvl_handle_compile_sing l n (bvl_Op closLang_op xs) =
      (let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
        if closLang_op = closLang_ThunkOp ForceThunk then
          (bvl_Op closLang_op ys,lx,s1 + 1,F) else
          OptionalLetLet_sing (bvl_Op closLang_op ys) n lx (s1 + 1) l
            nr1)) /\
   (bvl_handle_compile_sing l n (bvl_Tick x) =
      (let (y,lx,s1,nr1) = bvl_handle_compile_sing l n x in
        (bvl_Tick y,lx,s1,nr1))) /\
   (bvl_handle_compile_sing l n (bvl_Force m v) = (if v < n then
     (bvl_Force m v,db_vars_Var v,1,F) else (bvl_Op (closLang_IntOp
     (closLang_Const 0)) [],db_vars_Empty,1,T))) /\
   (bvl_handle_compile_sing l n (bvl_Call t dest xs) =
      (let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
        OptionalLetLet_sing (bvl_Call t dest ys) n lx (s1 + 1) l F))
          /\
   (bvl_handle_compile_list l n [] = (([]:bvl_exp
     list),db_vars_Empty,0,T)) /\
   (bvl_handle_compile_list l n (x :: xs) =
      (let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x in
      let (dy,ly,s2,nr2) = bvl_handle_compile_list l n xs in
        (dx :: dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2))))`;;

let compile_exp_def = cake_define
  `bvl_handle_compile_exp cut_size arity e =
     HD (FST (bvl_handle_compile cut_size arity [handle_simp
       (bvl_const_compile_exp e)]))`;;

(* HOL4 ML code, not ported:
val dest_Seq_def = PmatchHeuristics.with_classic_heuristic Define `
  (dest_Seq (Let [e1;e2] (Var 1)) = SOME (e1,e2)) /\
  (dest_Seq _ = NONE)`
*)

(* HOL4 termination: ( \\ strip_tac \\ HO_MATCH_MP_TAC (fetch "-"
   "dest_Seq_ind") \\ fs [dest_Seq_def] \\ EVAL_TAC \\ fs []):tactic *)
let compile_seqs_def = cake_define_wf
  `MEASURE (\(c,e,a). exp_size e)`
  `compile_seqs cut_size e acc =
     (match dest_Seq e with NONE -> (let new_e =
       bvl_handle_compile_exp cut_size 0 e in
                  match acc with NONE -> new_e | SOME rest -> bvl_Let
                    [new_e] (bvl_Let [] (bvl_Let [] rest))) | SOME
                    (e1,e2) ->
         compile_seqs cut_size e1
           (SOME (compile_seqs cut_size e2 acc)))`;;

let compile_any_def = cake_define
  `compile_any split_seq cut_size arity e =
     (if (arity = 0) /\ split_seq then
       compile_seqs cut_size e NONE else
       bvl_handle_compile_exp cut_size arity e)`;;
