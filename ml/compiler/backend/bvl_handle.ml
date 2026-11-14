(* ======================================================== *)
(*  bvl_handle: ported from HOL4's
    compiler/backend/bvl_handleScript.sml
    A definition theory, with 17 definitions and 8 theorems.  Needed
    by backend_passes.ml, bvl_handleProof.ml, bvl_inline.ml,
    bvl_inlineProof.ml and bvl_to_bvi.ml.  *)
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvl_handle"
  ["bvl"; "bvl_const"; "db_vars"];;

let _ = do_list hide_constant ["pmatch"];;

let can_raise_def,can_raise_ind = define_rec
  [`can_raise (bvl_Var v:bvl_exp) = F`;
   `can_raise (bvl_If x1 x2 x3:bvl_exp) = (can_raise x1 \/ can_raise
    x2 \/ can_raise x3)`;
   `can_raise (bvl_Let xs x2:bvl_exp) = (can_raise x2 \/ can_raise1
    xs)`;
   `can_raise (bvl_Handle x1 x2:bvl_exp) = can_raise x2`;
   `can_raise (bvl_Raise x1:bvl_exp) = T`;
   `can_raise (bvl_Op op xs:bvl_exp) = (op = closLang_ThunkOp
    ForceThunk \/ can_raise1 xs)`;
   `can_raise (bvl_Tick x:bvl_exp) = can_raise x`;
   `can_raise (bvl_Force m n:bvl_exp) = T`;
   `can_raise (bvl_Call t dest xs:bvl_exp) = T`;
   `can_raise1 [] = F`;
   `can_raise1 (CONS x xs) = (can_raise x \/ can_raise1 xs)`];;

let dest_handle_Raise_def = new_definition
  `dest_handle_Raise x1 =
      match x1 with
        (bvl_Raise x:bvl_exp) -> (if can_raise x then NONE else SOME
          x)
      | _1 -> NONE`;;

let dest_handle_Let_def = new_definition
  `dest_handle_Let x1 =
      match x1 with
        (bvl_Let xs x:bvl_exp) -> (if can_raise1 xs then NONE else
          SOME (xs,x))
      | _2 -> NONE`;;

let dest_handle_If_def = new_definition
  `dest_handle_If x1 =
      match x1 with
        (bvl_If x1 x2 x3:bvl_exp) ->
     (if can_raise x1 then NONE else
      if can_raise x2 then (if can_raise x3 then NONE else SOME (INL
        (x1,x2,x3))) else
      if can_raise x3 then (if can_raise x2 then NONE else SOME (INR
        (x1,x2,x3))) else
        NONE)
      | _3 -> NONE`;;

let handle_adj_vars_def,handle_adj_vars_ind = define_rec
  [`(handle_adj_vars l d (bvl_Var v:bvl_exp) = bvl_Var (if v < l then v
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
   (handle_adj_vars l d (bvl_Raise x1) = bvl_Raise (handle_adj_vars
     l d x1)) /\
   (handle_adj_vars l d (bvl_Op op xs) = bvl_Op op (handle_adj_vars1
     l d xs)) /\
   (handle_adj_vars l d (bvl_Tick x) = bvl_Tick (handle_adj_vars l d
     x)) /\
   (handle_adj_vars l d (bvl_Force m v) = bvl_Force m (if v < l then
     v else v + d)) /\
   (handle_adj_vars l d (bvl_Call t dest xs) =
      bvl_Call t dest (handle_adj_vars1 l d xs)) /\
   (handle_adj_vars1 l d [] = []) /\
   (handle_adj_vars1 l d (CONS x xs) = CONS (handle_adj_vars l d
     x) (handle_adj_vars1 l d xs))`];;

let handle_size_def,handle_size_ind = define_rec
  [`handle_size (bvl_Var v:bvl_exp) = 1`;
   `handle_size (bvl_If x1 x2 x3:bvl_exp) = 1 + handle_size x1 +
    handle_size x2 + handle_size x3`;
   `handle_size (bvl_Let xs x2:bvl_exp) = 1 + handle_size x2 +
    handle_size1 xs`;
   `handle_size (bvl_Handle x1 x2:bvl_exp) = 1 + 5 * (handle_size x1
    + handle_size x2)`;
   `handle_size (bvl_Raise x1:bvl_exp) = 1 + handle_size x1`;
   `handle_size (bvl_Op op xs:bvl_exp) = 1 + handle_size1 xs`;
   `handle_size (bvl_Tick x:bvl_exp) = 1 + handle_size x`;
   `handle_size (bvl_Force m n:bvl_exp) = 1`;
   `handle_size (bvl_Call t dest xs:bvl_exp) = 1 + handle_size1 xs`;
   `handle_size1 [] = (1:num)`;
   `handle_size1 (CONS x xs) = ((1 + handle_size x + handle_size1
    xs):num)`];;

(* [local] *)
let handle_size_non_zero = prove
 (`0 < handle_size x`,
  CHEAT_TAC);;

let handle_simp_def,handle_simp_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`handle_simp (bvl_Handle x1 x2:bvl_exp) = make_handle x1 x2 0`;
   `handle_simp (bvl_Var v:bvl_exp) = (bvl_Var v:bvl_exp)`;
   `handle_simp (bvl_If x1 x2 x3:bvl_exp) = bvl_If (handle_simp x1)
    (handle_simp x2) (handle_simp x3)`;
   `handle_simp (bvl_Let xs x2:bvl_exp) = bvl_Let (handle_simp_list
    xs) (handle_simp x2)`;
   `handle_simp (bvl_Raise x1:bvl_exp) = bvl_Raise (handle_simp x1)`;
   `handle_simp (bvl_Op op xs:bvl_exp) = bvl_Op op (handle_simp_list
    xs)`;
   `handle_simp (bvl_Tick x:bvl_exp) = bvl_Tick (handle_simp x)`;
   `handle_simp (bvl_Force m n:bvl_exp) = (bvl_Force m n:bvl_exp)`;
   `handle_simp (bvl_Call t dest xs:bvl_exp) = bvl_Call t dest
    (handle_simp_list xs)`;
   `handle_simp_list [] = ([]:bvl_exp list)`;
   `handle_simp_list (CONS x xs) = ((CONS (handle_simp x)
    (handle_simp_list xs)):bvl_exp list)`;
   `make_handle x1 x2 l =
         (match dest_handle_Raise x1 with SOME r -> bvl_Let [r]
             (handle_adj_vars 1 l (handle_simp x2)) | NONE ->
         (match dest_handle_Let x1 with SOME (xs,x) -> bvl_Let
             (handle_simp_list xs) (make_handle x x2 (l + LENGTH xs)) |
             NONE ->
         (match dest_handle_If x1 with SOME (INR (b1,b2,b3)) ->
             bvl_If (handle_simp b1)
                              (handle_simp b2)
                              (make_handle b3 x2 l) | SOME (INL
                                  (b1,b2,b3)) -> bvl_If (handle_simp b1)
                              (make_handle b2 x2 l)
                              (handle_simp b3) | NONE ->
                                  (bvl_Handle (handle_simp x1)
                                  (handle_adj_vars 1 l (handle_simp
                                  x2))))))`];;

let SmartLet_def = new_definition
  `SmartLet xs x = (if NULL xs then x else bvl_Let xs x)`;;

let LetLet_def = new_definition
  `LetLet env_length fvs (body:bvl_exp) =
     (let xs = list_of_seq I env_length in
     let zs = FILTER (\n. IS_SOME (sptree_lookup n fvs)) xs in
     let ys = MAPi (\i x. (x,i)) zs in
     let long_list = list_of_seq (\n. match ALOOKUP ys n with NONE ->
       bvl_Op (closLang_IntOp (closLang_Const (&0))) [] | SOME k ->
       bvl_Var k) env_length in
       bvl_Let (MAP bvl_Var zs) (SmartLet long_list body))`;;

let OptionalLetLet_def = new_definition
  `OptionalLetLet e env_size live s (limit':num) (nr:bool) =
     (if s < limit' then ([e],live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         ([(bvl_Let [] (LetLet env_size fvs e))],flat_live,0,nr))`;;

let OptionalLetLet_sing_def = new_definition
  `OptionalLetLet_sing e env_size live s (limit':num) (nr:bool) =
     (if s < limit' then (e,live,s,nr) else
       let fvs = db_to_set live in
       let flat_live = vars_from_list (MAP FST (toAList fvs)) in
         ((bvl_Let [] (LetLet env_size fvs e)),flat_live,0,nr))`;;

let OptionalLetLet_sing_eq = prove
 (`OptionalLetLet e sz lv s lim nr =
     (\(d,l,s,nr). ([d],l,s,nr)) (OptionalLetLet_sing e sz lv s lim
       nr)`,
  CHEAT_TAC);;

let _ = size_thms "bvl_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let bvl_handle_compile_def,bvl_handle_compile_ind = define_wf
  `MEASURE (\(x0,x1,x2). bvl_exp_size1 x2)`
  [`bvl_handle_compile l n [] = (([]:bvl_exp list),db_vars_Empty,0,T)`;
   `bvl_handle_compile l n (CONS x (CONS y xs)) =
         (let (dx,lx,s1,nr1) = bvl_handle_compile l n [x] in
         let (dy,ly,s2,nr2) = bvl_handle_compile l n (CONS y xs) in
           (APPEND dx dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2)))`;
   `bvl_handle_compile l n [(bvl_Var v:bvl_exp)] = (if v < n then
    ([bvl_Var v],db_vars_Var v,1,T) else ([bvl_Op (closLang_IntOp
    (closLang_Const (&0))) []],db_vars_Empty,1,T))`;
   `bvl_handle_compile l n [(bvl_If x1 x2 x3:bvl_exp)] =
         (let (x1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
         let (x2,l2,s2,nr2) = bvl_handle_compile l n [x2] in
         let (x3,l3,s3,nr3) = bvl_handle_compile l n [x3] in
           OptionalLetLet (bvl_If (HD x1) (HD x2) (HD x3)) n
             (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
             (nr1 /\ nr2 /\ nr3))`;
   `bvl_handle_compile l n [(bvl_Let xs x2:bvl_exp)] =
         (if NULL xs then
           bvl_handle_compile l n [x2] else
           let k = LENGTH xs in
           let (xs,l1,s1,nr1) = bvl_handle_compile l n xs in
           let (x2,l2,s2,nr2) = bvl_handle_compile l (n + k) [x2] in
             OptionalLetLet (bvl_Let xs (HD x2)) n
               (mk_Union l1 (db_vars_Shift k l2)) (s1 + s2 + 1) l
                   (nr1 /\ nr2))`;
   `bvl_handle_compile l n [(bvl_Handle x1 x2:bvl_exp)] =
         (let (y1,l1,s1,nr1) = bvl_handle_compile l n [x1] in
           if nr1 then (y1,l1,s1,T) else
             let (y2,l2,s2,nr2) = bvl_handle_compile l (n + 1) [x2]
                 in
               ([bvl_Handle (LetLet n (db_to_set l1) (HD y1)) (HD
                   y2)],
                mk_Union l1 (db_vars_Shift 1 l2),
                s2,
                   // s1 intentionally left out because
                   // it does not contrib to exp size in BVI
                   nr2))`;
   `bvl_handle_compile l n [(bvl_Raise x1:bvl_exp)] =
         (let (dx,lx,s1,nr1) = bvl_handle_compile l n [x1] in
           OptionalLetLet (bvl_Raise (HD dx)) n lx (s1 + 1) l F)`;
   `bvl_handle_compile l n [(bvl_Op op xs:bvl_exp)] =
         (let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
           if op = closLang_ThunkOp ForceThunk then
             ([bvl_Op op ys],lx,s1 + 1,F) else
             OptionalLetLet (bvl_Op op ys) n lx (s1 + 1) l nr1)`;
   `bvl_handle_compile l n [(bvl_Tick x:bvl_exp)] =
         (let (y,lx,s1,nr1) = bvl_handle_compile l n [x] in
           ([bvl_Tick (HD y)],lx,s1,nr1))`;
   `bvl_handle_compile l n [(bvl_Force m v:bvl_exp)] = (if v < n then
    ([(bvl_Force m v:bvl_exp)],db_vars_Var v,1,F) else ([bvl_Op
    (closLang_IntOp (closLang_Const (&0))) []],db_vars_Empty,1,T))`;
   `bvl_handle_compile l n [(bvl_Call t dest xs:bvl_exp)] =
         (let (ys,lx,s1,nr1) = bvl_handle_compile l n xs in
           OptionalLetLet (bvl_Call t dest ys) n lx (s1 + 1) l
               F)`];;

(* HOL4 bvl_handleScript.sml:214: ML code, not ported *)

let bvl_handle_compile_sing_def,bvl_handle_compile_sing_ind = define_rec
  [`bvl_handle_compile_sing l n (bvl_Var v:bvl_exp) = (if v < n then
    (bvl_Var v,db_vars_Var v,1,T) else (bvl_Op (closLang_IntOp
    (closLang_Const (&0))) [],db_vars_Empty,1,T))`;
   `bvl_handle_compile_sing l n (bvl_If x1 x2 x3:bvl_exp) =
         (let (x1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
         let (x2,l2,s2,nr2) = bvl_handle_compile_sing l n x2 in
         let (x3,l3,s3,nr3) = bvl_handle_compile_sing l n x3 in
           OptionalLetLet_sing ((bvl_If x1 x2 x3:bvl_exp)) n
             (mk_Union l1 (mk_Union l2 l3)) (s1 + s2 + s3 + 1) l
             (nr1 /\ nr2 /\ nr3))`;
   `bvl_handle_compile_sing l n (bvl_Let xs x2:bvl_exp) =
         (if NULL xs then
           bvl_handle_compile_sing l n x2 else
           let k = LENGTH xs in
           let (xs,l1,s1,nr1) = bvl_handle_compile_list l n xs in
           let (x2,l2,s2,nr2) = bvl_handle_compile_sing l (n + k) x2
               in
             OptionalLetLet_sing ((bvl_Let xs x2:bvl_exp)) n
               (mk_Union l1 (db_vars_Shift k l2)) (s1 + s2 + 1) l
                   (nr1 /\ nr2))`;
   `bvl_handle_compile_sing l n (bvl_Handle x1 x2:bvl_exp) =
         (let (y1,l1,s1,nr1) = bvl_handle_compile_sing l n x1 in
           if nr1 then (y1,l1,s1,T) else
             let (y2,l2,s2,nr2) = bvl_handle_compile_sing l (n + 1)
                 x2 in
               (bvl_Handle (LetLet n (db_to_set l1) y1) y2,
                mk_Union l1 (db_vars_Shift 1 l2),
                s2,
                   // s1 intentionally left out because
                   // it does not contrib to exp size in BVI
                   nr2))`;
   `bvl_handle_compile_sing l n (bvl_Raise x1:bvl_exp) =
         (let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x1 in
           OptionalLetLet_sing (bvl_Raise dx) n lx (s1 + 1) l F)`;
   `bvl_handle_compile_sing l n (bvl_Op op xs:bvl_exp) =
         (let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
           if op = closLang_ThunkOp ForceThunk then
             (bvl_Op op ys,lx,s1 + 1,F) else
             OptionalLetLet_sing (bvl_Op op ys) n lx (s1 + 1) l
                 nr1)`;
   `bvl_handle_compile_sing l n (bvl_Tick x:bvl_exp) =
         (let (y,lx,s1,nr1) = bvl_handle_compile_sing l n x in
           (bvl_Tick y,lx,s1,nr1))`;
   `bvl_handle_compile_sing l n (bvl_Force m v:bvl_exp) = (if v < n
    then ((bvl_Force m v:bvl_exp),db_vars_Var v,1,F) else (bvl_Op
    (closLang_IntOp (closLang_Const (&0))) [],db_vars_Empty,1,T))`;
   `bvl_handle_compile_sing l n (bvl_Call t dest xs:bvl_exp) =
         (let (ys,lx,s1,nr1) = bvl_handle_compile_list l n xs in
           OptionalLetLet_sing (bvl_Call t dest ys) n lx (s1 + 1)
               l F)`;
   `bvl_handle_compile_list l n [] = (([]:bvl_exp
    list),db_vars_Empty,0,T)`;
   `bvl_handle_compile_list l n (CONS x xs) =
         (let (dx,lx,s1,nr1) = bvl_handle_compile_sing l n x in
         let (dy,ly,s2,nr2) = bvl_handle_compile_list l n xs in
           (CONS dx dy,mk_Union lx ly,s1 + s2,(nr1 /\ nr2)))`];;

(* compile_sing_eq *)
let bvl_handle_compile_sing_eq = prove
 (`(!e l n. bvl_handle_compile l n [e] = (\(d,l,s,nr). ([d],l,s,nr))
  (bvl_handle_compile_sing l n e)) /\
   (!es l n. bvl_handle_compile l n es = bvl_handle_compile_list l
     n es)`,
  CHEAT_TAC);;

let bvl_handle_compile_exp_def = new_definition
  `bvl_handle_compile_exp cut_size arity e =
     HD (FST (bvl_handle_compile cut_size arity [handle_simp
       (bvl_const_compile_exp e)]))`;;

(* compile_exp_eq *)
let bvl_handle_compile_exp_eq = prove
 (`bvl_handle_compile_exp cut_size arity e =
     FST (bvl_handle_compile_sing cut_size arity (handle_simp
       (bvl_const_compile_exp e)))`,
  CHEAT_TAC);;

let dest_Seq_def = new_definition
  `bvl_handle_dest_Seq x1 =
        match x1 with
          (bvl_Let [e1; e2] (bvl_Var 1):bvl_exp) -> SOME (e1,e2)
        | _5 -> NONE`;;

let dest_Seq_pmatch = prove
 (`!exp.
   bvl_handle_dest_Seq exp =
     (match exp with
       bvl_Let [e1; e2] (bvl_Var 1) -> SOME (e1,e2) | _6 -> NONE)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvl_handleScript.sml:316-320: the tactic that proves the
   termination *)
let compile_seqs_def,compile_seqs_ind = define_wf
  `MEASURE (\(c,e,a). bvl_exp_size e)`
  [`compile_seqs cut_size e acc =
     (match bvl_handle_dest_Seq e with NONE -> (let new_e =
       bvl_handle_compile_exp cut_size 0 e in
                  match acc with NONE -> new_e | SOME rest ->
                    bvl_Let [new_e] (bvl_Let [] (bvl_Let [] rest))) |
                    SOME (e1,e2) ->
         compile_seqs cut_size e1
           (SOME (compile_seqs cut_size e2 acc)))`];;

let compile_any_def = new_definition
  `compile_any split_seq cut_size arity e =
     (if (arity = 0) /\ split_seq then
       compile_seqs cut_size e NONE else
       bvl_handle_compile_exp cut_size arity e)`;;

(* compile_length *)
let bvl_handle_compile_length = prove
 (`!l n xs. LENGTH (FST (bvl_handle_compile l n xs)) = LENGTH xs`,
  CHEAT_TAC);;
add_simp bvl_handle_compile_length;;

(* compile_sing *)
let bvl_handle_compile_sing = prove
 (`bvl_handle_compile l n [x] = (dx,lx,s) ==> (?y. dx = [y])`,
  CHEAT_TAC);;

(* HOL4 bvl_handleScript.sml:346-353: a theorem that HOL4 states as
   the value of an ML expression: compile_seqs_compute *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
