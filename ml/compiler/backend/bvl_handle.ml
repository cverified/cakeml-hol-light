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
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

let can_raise_def = cake_define_list
  [`can_raise (Var v:bvl_exp) = F`;
   `can_raise (If x1 x2 x3:bvl_exp) = (can_raise x1 \/ can_raise x2
  \/ can_raise x3)`;
   `can_raise (Let xs x2:bvl_exp) = (can_raise x2 \/ can_raise1 xs)`;
   `can_raise (Handle x1 x2:bvl_exp) = can_raise x2`;
   `can_raise (Raise x1:bvl_exp) = T`;
   `can_raise (Op op xs:bvl_exp) = (op = ThunkOp ForceThunk \/
  can_raise1 xs)`;
   `can_raise (Tick x:bvl_exp) = can_raise x`;
   `can_raise (Force m n:bvl_exp) = T`;
   `can_raise (Call t dest xs:bvl_exp) = T`;
   `can_raise1 [] = F`;
   `can_raise1 (x :: xs) = (can_raise x \/ can_raise1 xs)`];;

let dest_handle_Raise_def = cake_define
  `dest_handle_Raise x1 =
      match x1 with
        (Raise x:bvl_exp) -> (if can_raise x then NONE else SOME x)
      | _1 -> NONE`;;

let dest_handle_Let_def = cake_define
  `dest_handle_Let x1 =
      match x1 with
        (Let xs x:bvl_exp) -> (if can_raise1 xs then NONE else SOME
          (xs,x))
      | _2 -> NONE`;;

let dest_handle_If_def = cake_define
  `dest_handle_If x1 =
      match x1 with
        (If x1 x2 x3:bvl_exp) ->
     (if can_raise x1 then NONE else
      if can_raise x2 then (if can_raise x3 then NONE else SOME (INL
        (x1,x2,x3))) else
      if can_raise x3 then (if can_raise x2 then NONE else SOME (INR
        (x1,x2,x3))) else
        NONE)
      | _3 -> NONE`;;

let handle_adj_vars_def = cake_define_list
  [`handle_adj_vars l d (Var v:bvl_exp) = Var (if v < l then v else v
  + d)`;
   `handle_adj_vars l d (If x1 x2 x3:bvl_exp) =
         If (handle_adj_vars l d x1) (handle_adj_vars l d x2)
           (handle_adj_vars l d x3)`;
   `handle_adj_vars l d (Let xs x2:bvl_exp) =
         Let (handle_adj_vars1 l d xs) (handle_adj_vars (l +
           LENGTH xs) d x2)`;
   `handle_adj_vars l d (Handle x1 x2:bvl_exp) =
         Handle (handle_adj_vars l d x1) (handle_adj_vars (l + 1)
           d x2)`;
   `handle_adj_vars l d (Raise x1:bvl_exp) = Raise (handle_adj_vars l
  d x1)`;
   `handle_adj_vars l d (Op op xs:bvl_exp) = Op op (handle_adj_vars1
  l d xs)`;
   `handle_adj_vars l d (Tick x:bvl_exp) = Tick (handle_adj_vars l d
  x)`;
   `handle_adj_vars l d (Force m v:bvl_exp) = Force m (if v < l then
  v else v + d)`;
   `handle_adj_vars l d (Call t dest xs:bvl_exp) =
         Call t dest (handle_adj_vars1 l d xs)`;
   `handle_adj_vars1 l d [] = []`;
   `handle_adj_vars1 l d (x :: xs) = handle_adj_vars l d x ::
  handle_adj_vars1 l d xs`];;

let handle_size_def = cake_define_list
  [`handle_size (Var v:bvl_exp) = 1`;
   `handle_size (If x1 x2 x3:bvl_exp) = 1 + handle_size x1 +
  handle_size x2 + handle_size x3`;
   `handle_size (Let xs x2:bvl_exp) = 1 + handle_size x2 +
  handle_size1 xs`;
   `handle_size (Handle x1 x2:bvl_exp) = 1 + 5 * (handle_size x1 +
  handle_size x2)`;
   `handle_size (Raise x1:bvl_exp) = 1 + handle_size x1`;
   `handle_size (Op op xs:bvl_exp) = 1 + handle_size1 xs`;
   `handle_size (Tick x:bvl_exp) = 1 + handle_size x`;
   `handle_size (Force m n:bvl_exp) = 1`;
   `handle_size (Call t dest xs:bvl_exp) = 1 + handle_size1 xs`;
   `handle_size1 [] = (1:num)`;
   `handle_size1 (x :: xs) = 1 + handle_size x + handle_size1 xs`];;

let handle_simp_def = cake_define_list
  [`handle_simp (Handle x1 x2:bvl_exp) = make_handle x1 x2 0`;
   `handle_simp (Var v:bvl_exp) = Var v`;
   `handle_simp (If x1 x2 x3:bvl_exp) = If (handle_simp x1)
  (handle_simp x2) (handle_simp x3)`;
   `handle_simp (Let xs x2:bvl_exp) = Let (handle_simp_list xs)
  (handle_simp x2)`;
   `handle_simp (Raise x1:bvl_exp) = Raise (handle_simp x1)`;
   `handle_simp (Op op xs:bvl_exp) = Op op (handle_simp_list xs)`;
   `handle_simp (Tick x:bvl_exp) = Tick (handle_simp x)`;
   `handle_simp (Force m n:bvl_exp) = Force m n`;
   `handle_simp (Call t dest xs:bvl_exp) = Call t dest
  (handle_simp_list xs)`;
   `handle_simp_list [] = ([]:bvl_exp list)`;
   `handle_simp_list (x :: xs) = handle_simp x :: handle_simp_list xs`;
   `make_handle x1 x2 l =
         (match dest_handle_Raise x1 with SOME r -> Let [r]
           (handle_adj_vars 1 l (handle_simp x2)) | NONE ->
         (match dest_handle_Let x1 with SOME (xs,x) -> Let
           (handle_simp_list xs) (make_handle x x2 (l + LENGTH xs)) |
           NONE ->
         (match dest_handle_If x1 with SOME (INR (b1,b2,b3)) -> If
           (handle_simp b1)
                              (handle_simp b2)
                              (make_handle b3 x2 l) | SOME (INL
                                (b1,b2,b3)) -> If (handle_simp b1)
                              (make_handle b2 x2 l)
                              (handle_simp b3) | NONE -> (Handle
                                (handle_simp x1) (handle_adj_vars 1 l
                                (handle_simp x2))))))`];;

let SmartLet_def = cake_define
  `SmartLet xs x = (if NULL xs then x else Let xs x)`;;

let LetLet_def = cake_define
  `LetLet env_length fvs (body:bvl_exp) =
     (let xs = GENLIST I env_length in
     let zs = FILTER (\n. IS_SOME (sptree_lookup n fvs)) xs in
     let ys = MAPi (\i x. (x,i)) zs in
     let long_list = GENLIST (\n. match ALOOKUP ys n with NONE -> Op
       (closLang_IntOp (closLang_Const (&0))) [] | SOME k -> Var k)
       env_length in
       Let (MAP Var zs) (SmartLet long_list body))`;;

let OptionalLetLet_def = cake_define
  `OptionalLetLet e env_size live s (limit':num) (nr:bool) =
     (if s < limit' then ([e],live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         ([(Let [] (LetLet env_size fvs e))],flat_live,0,nr))`;;

let OptionalLetLet_sing_def = cake_define
  `OptionalLetLet_sing e env_size live s (limit':num) (nr:bool) =
     (if s < limit' then (e,live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         ((Let [] (LetLet env_size fvs e)),flat_live,0,nr))`;;

let compile_def = cake_define_list
  [`bvl_handle_compile l n [] = (([]:bvl_exp list),db_vars_Empty,0,T)`;
   `bvl_handle_compile l n (x :: y :: xs) =
         (let (dx,lx,s1,nr1) = bvl_handle_compile l n [x] in
         let (dy,ly,s2,nr2) = bvl_handle_compile l n (y :: xs) in
           (dx ++ dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2)))`;
   `bvl_handle_compile l n [(Var v:bvl_exp)] = (if v < n then ([Var
  v],Var v,1,T) else ([Op (closLang_IntOp (closLang_Const (&0)))
  []],db_vars_Empty,1,T))`;
   `bvl_handle_compile l n [(If x1 x2 x3:bvl_exp)] =
         (let (x1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
         let (x2,l2,s2,nr2) = bvl_handle_compile l n [x2] in
         let (x3,l3,s3,nr3) = bvl_handle_compile l n [x3] in
           OptionalLetLet (If (HD x1) (HD x2) (HD x3)) n
             (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
             (nr1 /\ nr2 /\ nr3))`;
   `bvl_handle_compile l n [(Let xs x2:bvl_exp)] =
         (if NULL xs then
           bvl_handle_compile l n [x2] else
           let k = LENGTH xs in
           let (xs,l1,s1,nr1) = bvl_handle_compile l n xs in
           let (x2,l2,s2,nr2) = bvl_handle_compile l (n + k) [x2] in
             OptionalLetLet (Let xs (HD x2)) n
               (mk_Union l1 (Shift k l2)) (s1 + s2 + 1) l (nr1 /\
                 nr2))`;
   `bvl_handle_compile l n [(Handle x1 x2:bvl_exp)] =
         (let (y1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
           if nr1 then (y1,l1,s1,T) else
             let (y2,l2,s2,nr2) = bvl_handle_compile l (n + 1) [x2]
               in
               ([Handle (LetLet n (db_to_set l1) (HD y1)) (HD y2)],
                mk_Union l1 (Shift 1 l2),
                s2,nr2))`;
   `bvl_handle_compile l n [(Raise x1:bvl_exp)] =
         (let (dx,lx,s1,nr1) = bvl_handle_compile l n [x1] in
           OptionalLetLet (Raise (HD dx)) n lx (s1 + 1) l F)`;
   `bvl_handle_compile l n [(Op op xs:bvl_exp)] =
         (let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
           if op = ThunkOp ForceThunk then
             ([Op op ys],lx,s1 + 1,F) else
             OptionalLetLet (Op op ys) n lx (s1 + 1) l nr1)`;
   `bvl_handle_compile l n [(Tick x:bvl_exp)] =
         (let (y,lx,s1,nr1) = bvl_handle_compile l n [x] in
           ([Tick (HD y)],lx,s1,nr1))`;
   `bvl_handle_compile l n [(Force m v:bvl_exp)] = (if v < n then
  ([Force m v],Var v,1,F) else ([Op (closLang_IntOp (closLang_Const
  (&0))) []],db_vars_Empty,1,T))`;
   `bvl_handle_compile l n [(Call t dest xs:bvl_exp)] =
         (let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
           OptionalLetLet (Call t dest ys) n lx (s1 + 1) l F)`];;
hol4_overload "compile" "bvl_handle_compile";;

(* HOL4 ML code, not ported:
val compile_ind = theorem"compile_ind";
*)

let compile_sing_def = cake_define_list
  [`bvl_handle_compile_sing l n (Var v:bvl_exp) = (if v < n then (Var
  v,Var v,1,T) else (Op (closLang_IntOp (closLang_Const (&0)))
  [],db_vars_Empty,1,T))`;
   `bvl_handle_compile_sing l n (If x1 x2 x3:bvl_exp) =
         (let (x1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
         let (x2,l2,s2,nr2) = bvl_handle_compile_sing l n x2 in
         let (x3,l3,s3,nr3) = bvl_handle_compile_sing l n x3 in
           OptionalLetLet_sing (If x1 x2 x3) n
             (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
             (nr1 /\ nr2 /\ nr3))`;
   `bvl_handle_compile_sing l n (Let xs x2:bvl_exp) =
         (if NULL xs then
           bvl_handle_compile_sing l n x2 else
           let k = LENGTH xs in
           let (xs,l1,s1,nr1) = bvl_handle_compile_list l n xs in
           let (x2,l2,s2,nr2) = bvl_handle_compile_sing l (n + k) x2
             in
             OptionalLetLet_sing (Let xs x2) n
               (mk_Union l1 (Shift k l2)) (s1 + s2 + 1) l (nr1 /\
                 nr2))`;
   `bvl_handle_compile_sing l n (Handle x1 x2:bvl_exp) =
         (let (y1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
           if nr1 then (y1,l1,s1,T) else
             let (y2,l2,s2,nr2) = bvl_handle_compile_sing l (n + 1)
               x2 in
               (Handle (LetLet n (db_to_set l1) y1) y2,
                mk_Union l1 (Shift 1 l2),
                s2,nr2))`;
   `bvl_handle_compile_sing l n (Raise x1:bvl_exp) =
         (let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x1 in
           OptionalLetLet_sing (Raise dx) n lx (s1 + 1) l F)`;
   `bvl_handle_compile_sing l n (Op op xs:bvl_exp) =
         (let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
           if op = ThunkOp ForceThunk then
             (Op op ys,lx,s1 + 1,F) else
             OptionalLetLet_sing (Op op ys) n lx (s1 + 1) l nr1)`;
   `bvl_handle_compile_sing l n (Tick x:bvl_exp) =
         (let (y,lx,s1,nr1) = bvl_handle_compile_sing l n x in
           (Tick y,lx,s1,nr1))`;
   `bvl_handle_compile_sing l n (Force m v:bvl_exp) = (if v < n then
  (Force m v,Var v,1,F) else (Op (closLang_IntOp (closLang_Const
  (&0))) [],db_vars_Empty,1,T))`;
   `bvl_handle_compile_sing l n (Call t dest xs:bvl_exp) =
         (let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
           OptionalLetLet_sing (Call t dest ys) n lx (s1 + 1) l
             F)`;
   `bvl_handle_compile_list l n [] = (([]:bvl_exp
  list),db_vars_Empty,0,T)`;
   `bvl_handle_compile_list l n (x :: xs) =
         (let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x in
         let (dy,ly,s2,nr2) = bvl_handle_compile_list l n xs in
           (dx :: dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2)))`];;
hol4_overload "compile_list" "bvl_handle_compile_list";;
hol4_overload "compile_sing" "bvl_handle_compile_sing";;

let compile_exp_def = cake_define
  `bvl_handle_compile_exp cut_size arity e =
     HD (FST (compile cut_size arity [handle_simp
       (bvl_const_compile_exp e)]))`;;
hol4_overload "compile_exp" "bvl_handle_compile_exp";;

let dest_Seq_def = cake_define
  `bvl_handle_dest_Seq x1 =
        match x1 with
          (Let [e1; e2] (Var 1):bvl_exp) -> SOME (e1,e2)
        | _4 -> NONE`;;
hol4_overload "dest_Seq" "bvl_handle_dest_Seq";;

let _ = size_thms "exp";;
(* HOL4 termination: ( \\ strip_tac \\ HO_MATCH_MP_TAC (fetch "-"
   "dest_Seq_ind") \\ fs [dest_Seq_def] \\ EVAL_TAC \\ fs []):tactic *)
let compile_seqs_def = cake_define_wf
  `MEASURE (\(c,e,a). exp_size e)`
  `compile_seqs cut_size e acc =
     (match bvl_handle_dest_Seq e with NONE -> (let new_e =
       compile_exp cut_size 0 e in
                  match acc with NONE -> new_e | SOME rest -> Let
                    [new_e] (Let [] (Let [] rest))) | SOME (e1,e2) ->
         compile_seqs cut_size e1
           (SOME (compile_seqs cut_size e2 acc)))`;;

let compile_any_def = cake_define
  `compile_any split_seq cut_size arity e =
     (if (arity = 0) /\ split_seq then
       compile_seqs cut_size e NONE else
       compile_exp cut_size arity e)`;;
