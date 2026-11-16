(* ======================================================== *)
(*  loop_live: ported from HOL4's
    pancake/loop_liveScript.sml
    A definition theory, with 6 definitions and 5 theorems.  Needed
    by crep_to_loop.ml, from_pancake32Prog.ml and
    from_pancake64Prog.ml.  *)
(* ======================================================== *)

(*
  Liveness analysis for loopLang.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "pancake/loopLang.ml";;
needs "pancake/loop_call.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "loop_live"
  ["loopLang"; "loop_call"];;

let _ = do_list hide_constant ["prog"];;


(* the clauses in two quotations: x is binop and exp, which one quotation
   cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL (x,_) -> loop_exp_size ARB x
                                   | INR (x,_) -> list_size (loop_exp_size ARB)
                                     x)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let vars_of_exp_def,vars_of_exp_ind = define_guess_clauses
  [`(vars_of_exp (loop_Var v) l = sptree_insert v one l) /\
    (vars_of_exp (loop_Const _) l = l) /\
    (vars_of_exp loop_BaseAddr l = l) /\
    (vars_of_exp loop_TopAddr l = l) /\
    (vars_of_exp (loop_Lookup _) l = l) /\
    (vars_of_exp (loop_Load a) l = vars_of_exp a l) /\
    (vars_of_exp (loop_Op x vs) l = vars_of_exp_list vs l)`;
   `(vars_of_exp (loop_Shift _ x y) l = vars_of_exp x (vars_of_exp y l)) /\
    (vars_of_exp_list xs l =
      (match xs with [] -> l
       | (CONS x xs) -> vars_of_exp x (vars_of_exp_list xs l)))`];;

let size_mk_BN = prove
 (`!t1 t2. sptree__size (mk_BN t1 t2) = sptree__size (BN t1 t2)`,
  CHEAT_TAC);;

let size_mk_BS = prove
 (`!t1 t2 x. sptree__size (mk_BS t1 x t2) = sptree__size (BS t1 x t2)`,
  CHEAT_TAC);;

let size_inter = prove
 (`!l1 l2. sptree__size (inter l1 l2) <= sptree__size l1`,
  CHEAT_TAC);;


let arith_vars = define_cases
  `(arith_vars (LLongMul r1 r2 r3 r4) l =
    sptree_insert r3 one (sptree_insert r4 one (sptree_delete r1
        (sptree_delete r2 l)))) /\
   (arith_vars (LDiv r1 r2 r3) l = sptree_insert r2 one (sptree_insert r3
    one (sptree_delete r1 l))) /\
   (arith_vars (LLongDiv r1 r2 r3 r4 r5) l =
    sptree_insert r3 one (sptree_insert r4 one (sptree_insert r5 one
        (sptree_delete r1 (sptree_delete r2 l)))))`;;

(* This optimisation shrinks all cutsets and also deletes assignments
   to unused variables. The Loop case is the interesting one: an
   auxiliary function is used to find a fixed-point. *)

(* the clauses in two quotations: n is num and mlstring; r is num and prog; x
   is ('a exp) and num, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     inv_image (MEASURE I LEX MEASURE I LEX MEASURE I)
                       (\x. match x with INL (_,c,_) -> (loop_prog_size (K 0)
                         c,(0:num),0)
                            | INR (_,live_in,l1,l2,body) ->
                                (loop_prog_size (K 0) body,1,sptree__size
                                  live_in - sptree__size l1))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 loop_liveScript.sml:149-160: the tactic that proves the termination *)
let loop_live_shrink_def,loop_live_shrink_ind = define_guess_clauses
  [`(loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Seq p1 p2) l =
         let (p2,l) = loop_live_shrink lt p2 l in
         let (p1,l) = loop_live_shrink lt p1 l in
           (loop_Seq p1 p2,l)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Loop live_in body live_out)
    l =
         let l2 = inter live_out l in
         let bex = sptree_union live_in l2 in
           match fixedpoint lt live_in LN bex body with SOME (body,l0) ->
               (let l = inter live_in l0 in (loop_Loop l body l2,l))
           | NONE -> let (b,_) = loop_live_shrink (CONS (live_in,l2) lt)
               body bex in
                       (loop_Loop live_in b l2,live_in)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_If x1 x2 x3 p1 p2 l1) l =
         let l = inter l l1 in
         let (p1,l1) = loop_live_shrink lt p1 l in
         let (p2,l2) = loop_live_shrink lt p2 l in
         let l3 = (match x3 with Reg r -> sptree_insert r one LN | _ -> LN)
             in
           (loop_If x1 x2 x3 p1 p2 l,sptree_insert x2 one (sptree_union
               l3 (sptree_union l1 l2)))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Mark p1) l =
    loop_live_shrink lt p1 l) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Break n) l =
         (loop_Break n,(match oEL n lt with SOME (_,brk) -> brk | NONE
             -> LN))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Continue n) l =
         (loop_Continue n,(match oEL n lt with SOME (cont,_) -> cont |
             NONE -> LN))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) loop_Fail l = (loop_Fail,LN)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) loop_Skip l = (loop_Skip,l)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Return vs) l =
    (loop_Return vs,list_insert vs LN)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Raise v) l = (loop_Raise
    v,sptree_insert v one LN)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Arith arith) l =
       (loop_Arith arith,arith_vars arith l)) /\
    // TODO: should we also do DCE for Primitive here, like the Assign case
    // below does?
    (loop_live_shrink b (loop_Primitive lhss pop rhss) l =
    (loop_Primitive lhss pop rhss,list_insert rhss (list_delete lhss
        l))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_LocValue n m) l =
         match sptree_lookup n l with NONE -> (loop_Skip,l)
         | SOME _ -> (loop_LocValue n m,sptree_delete n l)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Assign n x) l =
         match sptree_lookup n l with NONE -> (loop_Skip,l)
         | SOME _ -> (loop_Assign n x,vars_of_exp x (sptree_delete n
             l))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_ShMem op r ad) l =
       (loop_ShMem op r ad,
      // case lookup r l of
      // NONE => l
      // | _ => if is_load op
      // then vars_of_exp ad (insert r () l)
      // else l)
      vars_of_exp ad (sptree_insert r one l))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Store e n) l =
        (loop_Store e n,vars_of_exp e (sptree_insert n one l))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_SetGlobal name e) l =
        (loop_SetGlobal name e,vars_of_exp e l)) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) prog l = (prog,l))`;
   `(loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Call ret dest args handler)
    l =
         let a = fromAList (MAP (\x. (x,one)) args) in
         match ret with NONE -> (loop_Call NONE dest args NONE,sptree_union
             a l)
         | SOME (ns,l1) ->
            (match handler with NONE -> let l3 = (list_delete ns (inter l
                l1)) in
                        (loop_Call (SOME (ns,l3)) dest args
                            NONE,sptree_union a l3)
            | SOME (e,h,r,live_out) ->
                let (r,l2) = loop_live_shrink lt r l in
                let (h,l3) = loop_live_shrink lt h l in
                let l1 = inter l1 (sptree_union (list_delete ns l2)
                    (sptree_delete e l3)) in
                  (loop_Call (SOME (ns,l1)) dest args (SOME (e,h,r,inter l
                      live_out)),
                   sptree_union a l1))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_FFI n r1 r2 r3 r4 l1) l =
       (loop_FFI n r1 r2 r3 r4 (inter l1 l),
          sptree_insert r1 one (sptree_insert r2 one (sptree_insert r3
              one (sptree_insert r4 one (inter l1 l)))))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Load32 x y) l =
        (loop_Load32 x y,sptree_insert x one (sptree_delete y l))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_LoadByte x y) l =
        (loop_LoadByte x y,sptree_insert x one (sptree_delete y l))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_Store32 x y) l =
        (loop_Store32 x y,sptree_insert x one (sptree_insert y one l))) /\
    (loop_live_shrink (lt:(1 spt#1 spt) list) (loop_StoreByte x y) l =
        (loop_StoreByte x y,sptree_insert x one (sptree_insert y one
            l))) /\
    (fixedpoint (lt:(1 spt#1 spt) list) live_in l1 l2 body =
         let (b,l0) = loop_live_shrink (CONS (inter live_in l1,l2) lt) body
             l2 in
         let l0' = inter live_in l0 in
           if l0' = l1 then
                  // fixed point found!
                  SOME (b,l0) else if sptree__size l0' <= sptree__size l1
                      then
                    // no progress made, not possible
                    NONE else fixedpoint lt live_in l0' l2 body)`];;

let exp_ind =
  CAKE_GENL [`P`; `Q`] (SIMP_RULE [] (CAKE_SPECL [`\x l. P x`; `\x l. Q x`]
  vars_of_exp_ind));;

let fixedpoint_thm = prove
 (`!lt live_in l1 l2 (body:'a loop_prog) l0 b.
     fixedpoint lt live_in l1 l2 body = SOME (b,l0) ==>
     loop_live_shrink (CONS (inter live_in l0,l2) lt) body l2 = (b,l0)`,
  CHEAT_TAC);;

let mark_all_def,mark_all_ind = define_guess
  `mark_all prog =
     match prog with
       loop_Seq p1 p2 ->
        let (p1,t1) = mark_all p1 in
        let (p2,t2) = mark_all p2 in
        let t3 = (t1 /\ t2) in
          ((if t3 then loop_Mark (loop_Seq p1 p2) else loop_Seq p1 p2),t3)
     | loop_Loop l1 body l2 ->
        let (body,t1) = mark_all body in
          (loop_Loop l1 body l2,F)
     | loop_If x1 x2 x3 p1 p2 l1 ->
        let (p1,t1) = mark_all p1 in
        let (p2,t2) = mark_all p2 in
        let p3 = loop_If x1 x2 x3 p1 p2 l1 in
        let t3 = (t1 /\ t2) in
          ((if t3 then loop_Mark p3 else p3),t3)
     | loop_Mark p1 -> mark_all p1
     | loop_Call ret dest args handler ->
        (match handler with NONE -> (loop_Mark (loop_Call ret dest args
          handler),T)
        | SOME (ns,p1,p2,l) ->
            let (p1,t1) = mark_all p1 in
            let (p2,t2) = mark_all p2 in
            let t3 = (t1 /\ t2) in
            let p3 = loop_Call ret dest args (SOME (ns,p1,p2,l)) in
              ((if t3 then loop_Mark p3 else p3),t3))
     | prog -> (loop_Mark prog,T)`;;

let loop_live_comp_def = new_definition
  `loop_live_comp prog = FST (mark_all (FST (loop_live_shrink [] prog LN)))`;;

let loop_live_optimise_def = new_definition
  `loop_live_optimise prog = (loop_live_comp o FST o loop_call_comp LN) prog`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["prog"];;

(* and the interface *)
let _ = unhide_overloads ();;
