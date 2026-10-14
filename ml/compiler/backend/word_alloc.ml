(* ======================================================== *)
(*  word_alloc: ported from HOL4's
    compiler/backend/word_allocScript.sml  *)
(* ======================================================== *)

(*
  This is the compiler's register allocator. It supports different
    modes:
      0) simple allocator, no spill heuristics;
      1) simple allocator + spill heuristics;
      2) IRC allocator, no spill heuristics (default);
      3) IRC allocator + spill heuristics;
      4) linear scan register allocator.
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
(* HOL4 ancestors outside the port: (* for arity-2 Const *) *)

(* HOL4 overload (expanded in the port):
     Move0 = Move 0n *)
(* HOL4 overload (expanded in the port):
     Move1 = Move 1n *)

(*SSA form*)
let apply_nummap_key_def = cake_define
  `apply_nummap_key f names =
   fromAList (MAP (\(x,y). f x,y) (toAList names))`;;

let apply_nummaps_key_def = cake_define
  `apply_nummaps_key f names =
   (fromAList (MAP (\(x,y). f x,y) (toAList (FST names))),
    fromAList (MAP (\(x,y). f x,y) (toAList (SND names))))`;;

let option_lookup_def = cake_define
  `option_lookup t semanticPrimitives_v = (match sptree_lookup
  semanticPrimitives_v t with NONE -> 0 | SOME x -> x)`;;

let even_list_def = cake_define
  `(even_list = GENLIST (\x. 2 * x))`;;

(*Consistently sets up the next alloc variable rename for v*)
let next_var_rename_def = cake_define
  `next_var_rename semanticPrimitives_v ssa (na:num) =
  (na,sptree_insert semanticPrimitives_v na ssa,na + 4)`;;

let list_next_var_rename_def = cake_define
  `(list_next_var_rename [] ssa (na:num) = ([],ssa,na)) /\
   (list_next_var_rename (x :: xs) ssa na =
     (let (y,ssa',na') = next_var_rename x ssa na in
     let (ys,ssa'',na'') = list_next_var_rename xs ssa' na' in
       (y :: ys,ssa'',na'')))`;;

let fake_move_def = cake_define
  `fake_move semanticPrimitives_v = wordLang_Inst (wordLang_Const
  semanticPrimitives_v (n2w 0))`;;

(*Do the merging moves only*)
let merge_moves_def = cake_define
  `(word_alloc_merge_moves [] ssa_L ssa_R (na:num) =
  ([],[],na,ssa_L,ssa_R)) /\
   (word_alloc_merge_moves (x :: xs) ssa_L ssa_R na =
     (let (seqL,seqR,na',ssa_L',ssa_R') =
       word_alloc_merge_moves xs ssa_L ssa_R na in
     let optLx = sptree_lookup x ssa_L' in
     let optLy = sptree_lookup x ssa_R' in
     match (optLx,optLy) with
       (SOME Lx,SOME Ly) ->
       (if Lx = Ly then
         (seqL,seqR,na',ssa_L',ssa_R') else
         let Lmove = (na',Lx) in
         let Rmove = (na',Ly) in
         (Lmove :: seqL,Rmove :: seqR,na' + 4,
                              sptree_insert x na'
                                ssa_L',sptree_insert x na' ssa_R')) |
                                _1 -> (seqL,seqR,na',ssa_L',ssa_R')))`;;

(* tracking priority of moves
  0 = unprioritized
  1 = base "high" priority
  2 = higher priority than base

  T, INL <- left side
  F, INR <- right side
*)
let priority_def = cake_define
  `(priority NONE b = 1) /\
   (priority (SOME (INL one)) b =
     (if b then 2 else 1)) /\
   (priority (SOME (INR one)) b =
     (if b then 1 else 2))`;;

(*Separately do the fake moves*)
let fake_moves_def = cake_define
  `(fake_moves prio [] ssa_L ssa_R (na:num) = ((wordLang_Skip:'a
  wordLang_prog),(wordLang_Skip:'a wordLang_prog),na,ssa_L,ssa_R)) /\
   (fake_moves prio (x :: xs) ssa_L ssa_R na =
     (let (seqL,seqR,na',ssa_L',ssa_R') =
       fake_moves prio xs ssa_L ssa_R na in
     let optLx = sptree_lookup x ssa_L' in
     let optLy = sptree_lookup x ssa_R' in
     match (optLx,optLy) with
       (NONE,SOME Ly) ->
         (let Lmove = linear_scan_Seq seqL (fake_move na') in
         let Rmove = linear_scan_Seq seqR (wordLang_Move (priority
           prio F) [(na',Ly)]) in
         (Lmove,Rmove,na' + 4,sptree_insert x na'
           ssa_L',sptree_insert x na' ssa_R')) | (SOME Lx,NONE) ->
         (let Lmove = linear_scan_Seq seqL (wordLang_Move (priority
           prio T) [(na',Lx)]) in
         let Rmove = linear_scan_Seq seqR (fake_move na') in
         (Lmove,Rmove,na' + 4,sptree_insert x na'
           ssa_L',sptree_insert x na' ssa_R')) | _2 ->
           (seqL,seqR,na',ssa_L',ssa_R')))`;;

let fix_inconsistencies_def = cake_define
  `fix_inconsistencies prio ssa_L ssa_R na =
   (let var_union = MAP FST (toAList (sptree_union ssa_L ssa_R)) in
   let (Lmov,Rmov,na',ssa_L',ssa_R') =
     word_alloc_merge_moves var_union ssa_L ssa_R na in
   let (Lseq,Rseq,na'',ssa_L'',ssa_R'') =
     fake_moves prio var_union ssa_L' ssa_R' na' in
     (linear_scan_Seq (wordLang_Move (priority prio T) Lmov)
       Lseq,linear_scan_Seq (wordLang_Move (priority prio F) Rmov)
       Rseq,na'',ssa_L''))`;;

(*ssa_cc_trans_inst does not need to interact with stack*)
(* Note: this needs to return a prog to support specific registers for
   AddCarry and other special insts
*)
let ssa_cc_trans_inst_def = cake_define
  `ssa_cc_trans_inst x ssa na =
        match x with
          wordLang_Skip -> (wordLang_Skip,ssa,na)
        | (wordLang_Const asm_reg w) ->
       let (reg',ssa',na') = next_var_rename asm_reg ssa na in
         (wordLang_Inst (wordLang_Const reg' w),ssa',na')
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       match ri with
         Reg r3 ->
         (let r3' = option_lookup ssa r3 in
         let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_Arith (asm_Binop bop r1' r2' (Reg
             r3'))),ssa',na')) | _3 ->
         (let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_Arith (asm_Binop bop r1' r2'
             ri)),ssa',na'))
        | (asm_Arith (wordLang_Shift (backend_common_word_shift) r1
          r2 ri)) ->
       match ri with Reg r3 ->
         (let r3' = option_lookup ssa r3 in
         let r2' = option_lookup ssa r2 in
         let mov_in = (wordLang_Move 1) [(8,r3')] in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (linear_scan_Seq mov_in (wordLang_Inst (asm_Arith
             (wordLang_Shift (backend_common_word_shift) r1' r2' (Reg
             8)))),ssa',na')) | _4 ->
         (let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_Arith (wordLang_Shift
             (backend_common_word_shift) r1' r2' ri)),ssa',na'))
        | (asm_Arith (asm_Div r1 r2 r3)) ->
       let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       (wordLang_Inst (asm_Arith (asm_Div r1' r2' r3')),ssa',na')
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
       let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       let r4' = option_lookup ssa r4 in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let mov_in = (wordLang_Move 1) [(0,r4')] in
       let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r4'',0)] in
         (linear_scan_Seq mov_in (linear_scan_Seq (wordLang_Inst
           (asm_Arith (asm_AddCarry r1' r2' r3' 0)))
           mov_out),ssa'',na'')
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) ->
       let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r4'',0)] in
         (linear_scan_Seq (wordLang_Inst (asm_Arith (asm_AddOverflow
           r1' r2' r3' 0))) mov_out,ssa'',na'')
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) ->
       let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r4'',0)] in
         (linear_scan_Seq (wordLang_Inst (asm_Arith (asm_SubOverflow
           r1' r2' r3' 0))) mov_out,ssa'',na'')
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) ->
       let r3' = option_lookup ssa r3 in
       let r4' = option_lookup ssa r4 in
       let mov_in = (wordLang_Move 1) [(0,r3'); (4,r4')] in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r2',0); (r1',6)] in
         (linear_scan_Seq mov_in (linear_scan_Seq (wordLang_Inst
           (asm_Arith (asm_LongMul 6 0 0 4))) mov_out),ssa'',na'')
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) ->
       let r3' = option_lookup ssa r3 in
       let r4' = option_lookup ssa r4 in
       let r5' = option_lookup ssa r5 in
       let mov_in = (wordLang_Move 1) [(6,r3'); (0,r4')] in
       let (r2',ssa',na') = next_var_rename r2 ssa na in
       let (r1',ssa'',na'') = next_var_rename r1 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r2',6); (r1',0)] in
         (linear_scan_Seq mov_in (linear_scan_Seq (wordLang_Inst
           (asm_Arith (asm_LongDiv 0 6 6 0 r5'))) mov_out),ssa'',na'')
        | (asm_Mem wordLang_Load r (Addr a w)) ->
       let a' = option_lookup ssa a in
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_Mem wordLang_Load r' (Addr a'
           w)),ssa',na')
        | (asm_Mem wordLang_Store r (Addr a w)) ->
       let a' = option_lookup ssa a in
       let r' = option_lookup ssa r in
         (wordLang_Inst (asm_Mem wordLang_Store r' (Addr a'
           w)),ssa,na)
        | (asm_Mem asm_Load32 r (Addr a w)) ->
       let a' = option_lookup ssa a in
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_Mem asm_Load32 r' (Addr a' w)),ssa',na')
        | (asm_Mem asm_Store32 r (Addr a w)) ->
       let a' = option_lookup ssa a in
       let r' = option_lookup ssa r in
         (wordLang_Inst (asm_Mem asm_Store32 r' (Addr a' w)),ssa,na)
        | (asm_Mem asm_Load8 r (Addr a w)) ->
       let a' = option_lookup ssa a in
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_Mem asm_Load8 r' (Addr a' w)),ssa',na')
        | (asm_Mem asm_Store8 r (Addr a w)) ->
       let a' = option_lookup ssa a in
       let r' = option_lookup ssa r in
         (wordLang_Inst (asm_Mem asm_Store8 r' (Addr a' w)),ssa,na)
        | (asm_FP (FPLess r f1 f2)) ->
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_FP (FPLess r' f1 f2)),ssa',na')
        | (asm_FP (FPLessEqual r f1 f2)) ->
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_FP (FPLessEqual r' f1 f2)),ssa',na')
        | (asm_FP (FPEqual r f1 f2)) ->
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_FP (FPEqual r' f1 f2)),ssa',na')
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       if dimindex (:'a) = 64 then
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_FP (FPMovToReg r1' r2 d)),ssa',na')
             else
         let (r1',ssa',na') = next_var_rename r1 ssa na in
         let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
           (wordLang_Inst (asm_FP (FPMovToReg r1' r2' d)),ssa'',na'')
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       if dimindex (:'a) = 64 then
         let r1' = option_lookup ssa r1 in
           (wordLang_Inst (asm_FP (FPMovFromReg d r1' 0)),ssa,na)
             else
         let r1' = option_lookup ssa r1 in
         let r2' = option_lookup ssa r2 in
         if r1' = r2' then
           let (r2'',ssa',na') = next_var_rename r2 ssa na in
           let mov_in = (wordLang_Move 0) [(r2'',r2')] in
           (linear_scan_Seq mov_in (wordLang_Inst (asm_FP
             (FPMovFromReg d r1' r2''))),
           ssa',na') else
           (wordLang_Inst (asm_FP (FPMovFromReg d r1' r2')),ssa,na)
        | x -> (wordLang_Inst x,ssa,na)`;;

(*Expressions only ever need to lookup a variable's current ssa map
  so it doesn't need the other parts *)
let ssa_cc_trans_exp_def = cake_define
  `ssa_cc_trans_exp t expr =
        match expr with
          (wordLang_Var num) ->
       wordLang_Var (option_lookup t num)
        | (wordLang_Load wordLang_exp) -> wordLang_Load
          (ssa_cc_trans_exp t wordLang_exp)
        | (wordLang_Op wop ls) ->
       wordLang_Op wop (MAP (ssa_cc_trans_exp t) ls)
        | (wordLang_Shift sh wordLang_exp nexp) ->
       wordLang_Shift sh (ssa_cc_trans_exp t wordLang_exp)
         (ssa_cc_trans_exp t nexp)
        | expr -> expr`;;

(*Attempt to pull out "renaming" moves
  This takes a current name map and updates the names of all the vars
  Intended for Alloc,Call cutset restoration moves
*)
let list_next_var_rename_move_def = cake_define
  `list_next_var_rename_move ssa n ls =
     (let cur_ls = MAP (option_lookup ssa) ls in
     let (new_ls,ssa',n') = list_next_var_rename ls ssa n in
     ((wordLang_Move 0) (ZIP (new_ls,cur_ls)),ssa',n'))`;;

(* force the renaming map to send x -> y unless
  x is already remapped *)
let force_rename_def = cake_define
  `(force_rename [] ssa = ssa) /\
   (force_rename ((x,y) :: xs) ssa =
     force_rename xs (sptree_insert x y ssa))`;;

let mk_prio_def = cake_define
  `mk_prio el er =
   (if el = wordLang_Skip then SOME (INL one) else if er =
     wordLang_Skip then SOME (INR one) else NONE)`;;

(*Generate reconciliation moves from current ssa to target ssa for vars
   in ns.

  For v ∈ ns ∩ domain cur_ssa: emit a Move from cur_ssa(v) to tgt_ssa(v)
  (skipped if they happen to be the same register).

  For v ∈ ns with v ∉ domain cur_ssa: emit nothing. Such v are vacuous
  in strong_locals_rel (ssa_locals_rel ⇒ v ∉ domain st.locals), and when
  the enclosing Loop's cut_state reads tgt_ssa(v), it either succeeds
  because v was added to cur_ssa later (so Case 3 in the proof analysis
  applies: position tgt_ssa(v) = v gets moved), or the source cut also
  fails, making the theorem vacuous.*)
let ssa_reconcile_def = cake_define
  `ssa_reconcile cur_ssa tgt_ssa ns =
     (let vars = MAP FST (toAList ns) in
     let moves = FILTER (\(a,b). ~(a = b))
       (FLAT (MAP (\semanticPrimitives_v.
         match sptree_lookup semanticPrimitives_v cur_ssa with NONE
           -> [] | SOME cur_v -> [(option_lookup tgt_ssa
           semanticPrimitives_v,cur_v)]) vars)) in
     if moves = [] then (wordLang_Skip:'a wordLang_prog) else
       wordLang_Move 1 moves)`;;

(* Loop entry setup: refresh ssa for vars in (names ∪ exit_names) so
   that
   option_lookup ssa_refreshed is INJ on each. For vars already in ssa
     we
   emit a real Move; for vars not in ssa we allocate fresh ssa entries
   and fake_move-initialise the corresponding target registers. *)
let loop_setup_def = cake_define
  `loop_setup (names:one spt) (exit_names:one spt) ssa na =
     (let all_vars_ls = MAP FST (toAList (sptree_union names
       exit_names)) in
     let extend_ls = FILTER (\semanticPrimitives_v. sptree_lookup
       semanticPrimitives_v ssa = NONE) all_vars_ls in
     let refresh_ls = FILTER (\semanticPrimitives_v. IS_SOME
       (sptree_lookup semanticPrimitives_v ssa)) all_vars_ls in
     let (fresh_pos_ls,ssa_ext,na_ext) =
       list_next_var_rename extend_ls ssa na in
     let fake_prog = ITLIST linear_scan_Seq
       (MAP (\r. fake_move r) fresh_pos_ls) (wordLang_Skip:'a
         wordLang_prog) in
     let (refresh_mov,ssa_refreshed,na_refreshed) =
       list_next_var_rename_move ssa_ext na_ext refresh_ls in
     (linear_scan_Seq fake_prog
       refresh_mov,ssa_refreshed,na_refreshed))`;;

let ssa_cc_trans_def = cake_define
  `(ssa_cc_trans wordLang_Skip ssa na lt = (wordLang_Skip,ssa,na)) /\
   (ssa_cc_trans (wordLang_Move pri ls) ssa na lt =
     (let ls_1 = MAP FST ls in
     let ls_2 = MAP SND ls in
     let ren_ls2 = MAP (option_lookup ssa) ls_2 in
     let (ren_ls1,ssa',na') = list_next_var_rename ls_1 ssa na in
     let force =
       FILTER (\(x,y). ~MEM x ls_1) (ZIP (ls_2,ren_ls1)) in
       (wordLang_Move pri (ZIP (ren_ls1,ren_ls2)),force_rename force
         ssa',na'))) /\
   (ssa_cc_trans (wordLang_StoreConsts a b c d ws) ssa na lt =
     (let c1 = option_lookup ssa c in
     let d1 = option_lookup ssa d in
     let (d2,ssa',na') = next_var_rename d ssa na in
     let (c2,ssa'',na'') = next_var_rename c ssa' na' in
     let wordLang_prog = linear_scan_Seq ((wordLang_Move 1) [(4,c1);
       (6,d1)])
       (linear_scan_Seq (wordLang_StoreConsts 0 2 4 6 ws)
            ((wordLang_Move 1) [(c2,4); (d2,6)])) in
     (wordLang_prog,ssa'',na''))) /\
   (ssa_cc_trans (wordLang_Inst i) ssa na lt =
     (let (i',ssa',na') = ssa_cc_trans_inst i ssa na in
       (i',ssa',na'))) /\
   (ssa_cc_trans (wordLang_Assign num' wordLang_exp) ssa na lt =
     (let exp' = ssa_cc_trans_exp ssa wordLang_exp in
     let (num',ssa',na') = next_var_rename num' ssa na in
       (wordLang_Assign num' exp',ssa',na'))) /\
   (ssa_cc_trans (wordLang_Get num' store) ssa na lt =
     (let (num',ssa',na') = next_var_rename num' ssa na in
       (wordLang_Get num' store,ssa',na'))) /\
   (ssa_cc_trans (wordLang_Store wordLang_exp num') ssa na lt =
     (let exp' = ssa_cc_trans_exp ssa wordLang_exp in
     let num' = option_lookup ssa num' in
       (wordLang_Store exp' num',ssa,na))) /\
   (ssa_cc_trans (linear_scan_Seq s1 s2) ssa na lt =
     (let (s1',ssa',na') = ssa_cc_trans s1 ssa na lt in
     let (s2',ssa'',na'') = ssa_cc_trans s2 ssa' na' lt in
       (linear_scan_Seq s1' s2',ssa'',na''))) /\
   (ssa_cc_trans (wordLang_MustTerminate s1) ssa na lt =
     (let (s1',ssa',na') = ssa_cc_trans s1 ssa na lt in
       (wordLang_MustTerminate s1',ssa',na'))) /\
   (ssa_cc_trans (wordLang_If cmp r1 ri e2 e3) ssa na lt =
     (let r1' = option_lookup ssa r1 in
     let ri' = match ri with Reg r -> Reg (option_lookup ssa r) | Imm
       semanticPrimitives_v -> Imm semanticPrimitives_v in
     let (e2',ssa2,na2) = ssa_cc_trans e2 ssa na lt in
     let (e3',ssa3,na3) = ssa_cc_trans e3 ssa na2 lt in
     let prio = mk_prio e2' e3' in
     let (e2_cons,e3_cons,na_fin,ssa_fin) =
       fix_inconsistencies prio ssa2 ssa3 na3 in
     (wordLang_If cmp r1' ri' (linear_scan_Seq e2' e2_cons)
       (linear_scan_Seq e3' e3_cons),ssa_fin,na_fin))) /\
   (ssa_cc_trans (wordLang_Alloc num' numset) ssa na lt =
     (let all_names' = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList all_names') in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na +
       2) ls in
     let num' = option_lookup ssa' num' in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let ssa_cut = inter ssa' all_names' in
     let (ret_mov,ssa'',na'') =
       list_next_var_rename_move ssa_cut (na' + 2) ls in
     let wordLang_prog = (linear_scan_Seq (stack_mov)
                (linear_scan_Seq ((wordLang_Move 1) [(2,num')])
                (linear_scan_Seq (wordLang_Alloc 2 stack_set)
                  (ret_mov)))) in
     (wordLang_prog,ssa'',na''))) /\
   (ssa_cc_trans (wordLang_Raise num') ssa na lt =
     (let num' = option_lookup ssa num' in
     let mov = (wordLang_Move 1) [(2,num')] in
     (linear_scan_Seq mov (wordLang_Raise 2),ssa,na))) /\
   (ssa_cc_trans (wordLang_OpCurrHeap b dst src) ssa na lt =
     (let src' = option_lookup ssa src in
     let (dst',ssa',na') = next_var_rename dst ssa na in
       (wordLang_OpCurrHeap b dst' src',ssa',na'))) /\
   (ssa_cc_trans (wordLang_Return num' nums) ssa na lt =
     (let num' = option_lookup ssa num' in
     let nums' = MAP (option_lookup ssa) nums in
     let rets = GENLIST (\x. 2 * (x + 1)) (LENGTH nums') in
     let mov = wordLang_Move 0 (ZIP (rets,nums')) in
     (linear_scan_Seq mov (wordLang_Return num' rets),ssa,na))) /\
   (ssa_cc_trans wordLang_Tick ssa na lt = (wordLang_Tick,ssa,na)) /\
   (ssa_cc_trans (reg_alloc_Set n wordLang_exp) ssa na lt =
     (let exp' = ssa_cc_trans_exp ssa wordLang_exp in
     (reg_alloc_Set n exp',ssa,na))) /\
   (ssa_cc_trans (wordLang_LocValue r l1) ssa na lt =
     (let (r',ssa',na') = next_var_rename r ssa na in
       (wordLang_LocValue r' l1,ssa',na'))) /\
   (ssa_cc_trans (wordLang_Install ptr len dptr dlen numset) ssa na
     lt =
     (let all_names' = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList all_names') in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na +
       2) ls in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let ptr' = option_lookup ssa' ptr in
     let len' = option_lookup ssa' len in
     let dptr' = option_lookup ssa' dptr in
     let dlen' = option_lookup ssa' dlen in
     let ssa_cut = inter ssa' all_names' in
     let (ptr'',ssa'',na'') = next_var_rename ptr ssa_cut (na' + 2)
       in
     let (ret_mov,ssa''',na''') =
       list_next_var_rename_move ssa'' na'' ls in
     let wordLang_prog = (linear_scan_Seq (stack_mov)
                (linear_scan_Seq ((wordLang_Move 1) [(2,ptr');
                  (4,len')])
                (linear_scan_Seq (wordLang_Install 2 4 dptr' dlen'
                  stack_set)
                (linear_scan_Seq ((wordLang_Move 1) [(ptr'',2)])
                  ret_mov)))) in
     (wordLang_prog,ssa''',na'''))) /\
   (ssa_cc_trans (wordLang_CodeBufferWrite r1 r2) ssa na lt =
     (let r1' = option_lookup ssa r1 in
     let r2' = option_lookup ssa r2 in
     (wordLang_CodeBufferWrite r1' r2',ssa,na))) /\
   (ssa_cc_trans (wordLang_DataBufferWrite r1 r2) ssa na lt =
     (let r1' = option_lookup ssa r1 in
     let r2' = option_lookup ssa r2 in
     (wordLang_DataBufferWrite r1' r2',ssa,na))) /\
   (ssa_cc_trans (wordLang_FFI ffi_index ptr1 len1 ptr2 len2 numset)
     ssa na lt =
     (let all_names' = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList all_names') in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na +
       2) ls in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let cptr1 = option_lookup ssa' ptr1 in
     let clen1 = option_lookup ssa' len1 in
     let cptr2 = option_lookup ssa' ptr2 in
     let clen2 = option_lookup ssa' len2 in
     let ssa_cut = inter ssa' all_names' in
     let (ret_mov,ssa'',na'') =
       list_next_var_rename_move ssa_cut (na' + 2) ls in
     let wordLang_prog = (linear_scan_Seq (stack_mov)
                (linear_scan_Seq ((wordLang_Move 1) [(2,cptr1);
                  (4,clen1); (6,cptr2); (8,clen2)])
                (linear_scan_Seq (wordLang_FFI ffi_index 2 4 6 8
                  stack_set) (ret_mov)))) in
     (wordLang_prog,ssa'',na''))) /\
   (ssa_cc_trans (wordLang_Call NONE dest args h) ssa na lt =
     (let names = MAP (option_lookup ssa) args in
     let conv_args = GENLIST (\x. 2 * x) (LENGTH names) in
     let move_args = ((wordLang_Move 1) (ZIP (conv_args,names))) in
     let wordLang_prog = linear_scan_Seq move_args (wordLang_Call
       NONE dest conv_args h) in
       (wordLang_prog,ssa,na))) /\
   (ssa_cc_trans (wordLang_Call (SOME (ret,numset,ret_handler,l1,l2))
     dest args h) ssa na lt =
     (let all_names' = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList all_names') in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na +
       2) ls in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let names = MAP (option_lookup ssa) args in
     let conv_args = GENLIST (\x. 2 * (x + 1)) (LENGTH names) in
     let move_args = ((wordLang_Move 1) (ZIP (conv_args,names))) in
     let ssa_cut = inter ssa' all_names' in
     let (ret_mov,ssa'',na'') =
       list_next_var_rename_move ssa_cut (na' + 2) ls in
     let (ret',ssa_2_p,na_2_p) = list_next_var_rename ret ssa'' na''
       in
     let (ren_ret_handler,ssa_2,na_2) =
       ssa_cc_trans ret_handler ssa_2_p na_2_p lt in
     let regs = GENLIST (\x. 2 * (x + 1)) (LENGTH ret) in
     let mov_ret_handler =
         (linear_scan_Seq ret_mov (linear_scan_Seq ((wordLang_Move 1)
           (ZIP (ret',regs))) (ren_ret_handler))) in
     (match h with
       NONE ->
         (let wordLang_prog =
           (linear_scan_Seq stack_mov (linear_scan_Seq move_args
           (wordLang_Call (SOME
             (regs,stack_set,mov_ret_handler,l1,l2))
                 dest conv_args NONE))) in
         (wordLang_prog,ssa_2,na_2)) | SOME (n,h,l1',l2') ->
         (let (n',ssa_3_p,na_3_p) = next_var_rename n ssa'' na_2 in
         let (ren_exc_handler,ssa_3,na_3) =
             (ssa_cc_trans h ssa_3_p na_3_p lt) in
         let mov_exc_handler =
             (linear_scan_Seq ret_mov (linear_scan_Seq
               ((wordLang_Move 1) [n',2]) (ren_exc_handler))) in
         let prio = mk_prio mov_ret_handler mov_exc_handler in
         let (ret_cons,exc_cons,na_fin,ssa_fin) =
             fix_inconsistencies prio ssa_2 ssa_3 na_3 in
         let cons_ret_handler = linear_scan_Seq mov_ret_handler
           ret_cons in
         let cons_exc_handler = linear_scan_Seq mov_exc_handler
           exc_cons in
         let wordLang_prog =
             (linear_scan_Seq stack_mov (linear_scan_Seq move_args
             (wordLang_Call (SOME
               (regs,stack_set,cons_ret_handler,l1,l2))
                dest conv_args (SOME (2,cons_exc_handler,l1',l2')))))
                  in
         (wordLang_prog,ssa_fin,na_fin))))) /\
   (ssa_cc_trans (wordLang_ShareInst ast_op semanticPrimitives_v
     wordLang_exp) ssa na lt =
     (let exp' = ssa_cc_trans_exp ssa wordLang_exp in
       if ast_op = wordLang_Store \/ ast_op = asm_Store8 \/ ast_op =
         asm_Store16 \/ ast_op = asm_Store32 then
         (wordLang_ShareInst ast_op (option_lookup ssa
           semanticPrimitives_v) exp',ssa,na) else
         let (v',ssa',na') = next_var_rename semanticPrimitives_v ssa
           na in
           (wordLang_ShareInst ast_op v' exp',ssa',na'))) /\
   (ssa_cc_trans (wordLang_Loop names body exit_names) ssa na lt =
     (let (setup_prog,ssa_refreshed,na_refreshed) =
       loop_setup names exit_names ssa na in
     let ssa_names = apply_nummap_key (option_lookup ssa_refreshed)
       names in
     let ssa_exit = apply_nummap_key (option_lookup ssa_refreshed)
       exit_names in
     let ssa_body = inter ssa_refreshed names in
     let (body',ssa',na') =
       ssa_cc_trans body ssa_body na_refreshed
         ((ssa_refreshed,names,exit_names) :: lt) in
     let back_moves = ssa_reconcile ssa' ssa_refreshed names in
     let body_final = if back_moves = wordLang_Skip then body' else
       linear_scan_Seq body' back_moves in
     (linear_scan_Seq setup_prog (wordLang_Loop ssa_names body_final
       ssa_exit),
      inter ssa_refreshed exit_names,na'))) /\
   (ssa_cc_trans (wordLang_Break n) ssa na lt =
     (match oEL n lt with
       NONE -> (wordLang_Break n,ssa,na) | SOME
         (tgt_ssa,names,exit_names) ->
         (let moves = ssa_reconcile ssa tgt_ssa exit_names in
         (if moves = wordLang_Skip then wordLang_Break n else
           linear_scan_Seq moves (wordLang_Break n),ssa,na)))) /\
   (ssa_cc_trans (wordLang_Continue n) ssa na lt =
     (match oEL n lt with
       NONE -> (wordLang_Continue n,ssa,na) | SOME
         (tgt_ssa,names,exit_names) ->
         (let moves = ssa_reconcile ssa tgt_ssa names in
         (if moves = wordLang_Skip then wordLang_Continue n else
           linear_scan_Seq moves (wordLang_Continue n),ssa,na))))`;;

(*Recursively applying colours to a program*)

let apply_colour_exp_def = cake_define
  `apply_colour_exp f expr =
        match expr with
          (wordLang_Var num) -> wordLang_Var (f num)
        | (wordLang_Load wordLang_exp) -> wordLang_Load
          (apply_colour_exp f wordLang_exp)
        | (wordLang_Op wop ls) -> wordLang_Op wop (MAP
          (apply_colour_exp f) ls)
        | (wordLang_Shift sh wordLang_exp nexp) -> wordLang_Shift sh
          (apply_colour_exp f wordLang_exp) (apply_colour_exp f nexp)
        | expr -> expr`;;

let apply_colour_imm_def = cake_define
  `apply_colour_imm f x =
        match x with
          (Reg n) -> Reg (f n)
        | x -> x`;;

let apply_colour_inst_def = cake_define
  `(apply_colour_inst f wordLang_Skip = wordLang_Skip) /\
   (apply_colour_inst f (wordLang_Const asm_reg w) = wordLang_Const
     (f asm_reg) w) /\
   (apply_colour_inst f (asm_Arith (asm_Binop bop r1 r2 ri)) =
     asm_Arith (asm_Binop bop (f r1) (f r2) (apply_colour_imm f ri)))
       /\
   (apply_colour_inst f (asm_Arith (wordLang_Shift
     (backend_common_word_shift) r1 r2 ri)) =
     asm_Arith (wordLang_Shift (backend_common_word_shift) (f r1) (f
       r2) (apply_colour_imm f ri))) /\
   (apply_colour_inst f (asm_Arith (asm_Div r1 r2 r3)) =
     asm_Arith (asm_Div (f r1) (f r2) (f r3))) /\
   (apply_colour_inst f (asm_Arith (asm_AddCarry r1 r2 r3 r4)) =
     asm_Arith (asm_AddCarry (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) =
     asm_Arith (asm_AddOverflow (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) =
     asm_Arith (asm_SubOverflow (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (asm_LongMul r1 r2 r3 r4)) =
     asm_Arith (asm_LongMul (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) =
     asm_Arith (asm_LongDiv (f r1) (f r2) (f r3) (f r4) (f r5))) /\
   (apply_colour_inst f (asm_Mem wordLang_Load r (Addr a w)) =
     asm_Mem wordLang_Load (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (asm_Mem wordLang_Store r (Addr a w)) =
     asm_Mem wordLang_Store (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (asm_Mem asm_Load32 r (Addr a w)) =
     asm_Mem asm_Load32 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (asm_Mem asm_Store32 r (Addr a w)) =
     asm_Mem asm_Store32 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (asm_Mem asm_Load8 r (Addr a w)) =
     asm_Mem asm_Load8 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (asm_Mem asm_Store8 r (Addr a w)) =
     asm_Mem asm_Store8 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (asm_FP (FPLess r f1 f2)) = asm_FP (FPLess (f
     r) f1 f2)) /\
   (apply_colour_inst f (asm_FP (FPLessEqual r f1 f2)) = asm_FP
     (FPLessEqual (f r) f1 f2)) /\
   (apply_colour_inst f (asm_FP (FPEqual r f1 f2)) = asm_FP (FPEqual
     (f r) f1 f2)) /\
   (apply_colour_inst f (asm_FP (FPMovToReg r1 r2 d)) = asm_FP
     (FPMovToReg (f r1) (f r2) d)) /\
   (apply_colour_inst f (asm_FP (FPMovFromReg d r1 r2)) = asm_FP
     (FPMovFromReg d (f r1) (f r2))) /\
   ((apply_colour_inst f x = x)
   End
   Definition apply_colour_def [simp]:(apply_colour f wordLang_Skip =
     wordLang_Skip)) /\
   (apply_colour f (wordLang_Move pri ls) =
     wordLang_Move pri (ZIP (MAP (f o FST) ls,MAP (f o SND) ls))) /\
   (apply_colour f (wordLang_Inst i) = wordLang_Inst
     (apply_colour_inst f i)) /\
   (apply_colour f (wordLang_Assign num wordLang_exp) =
     wordLang_Assign (f num) (apply_colour_exp f wordLang_exp)) /\
   (apply_colour f (wordLang_Get num store) = wordLang_Get (f num)
     store) /\
   (apply_colour f (wordLang_Store wordLang_exp num) = wordLang_Store
     (apply_colour_exp f wordLang_exp) (f num)) /\
   (apply_colour f (wordLang_Call ret dest args h) =
     (let ret = match ret with NONE -> NONE | SOME
       (vs,cutset,ret_handler,l1,l2) ->
                           SOME (MAP f vs,apply_nummaps_key f
                             cutset,apply_colour f ret_handler,l1,l2) in
     let args = MAP f args in
     let h = match h with NONE -> NONE | SOME
       (semanticPrimitives_v,wordLang_prog,l1,l2) -> SOME (f
       semanticPrimitives_v,apply_colour f wordLang_prog,l1,l2) in
       wordLang_Call ret dest args h)) /\
   (apply_colour f (linear_scan_Seq s1 s2) = linear_scan_Seq
     (apply_colour f s1) (apply_colour f s2)) /\
   (apply_colour f (wordLang_MustTerminate s1) =
     wordLang_MustTerminate (apply_colour f s1)) /\
   (apply_colour f (wordLang_If cmp r1 ri e2 e3) =
     wordLang_If cmp (f r1) (apply_colour_imm f ri) (apply_colour f
       e2) (apply_colour f e3)) /\
   (apply_colour f (wordLang_Install r1 r2 r3 r4 numset) =
     wordLang_Install (f r1) (f r2) (f r3) (f r4) (apply_nummaps_key
       f numset)) /\
   (apply_colour f (wordLang_CodeBufferWrite r1 r2) =
     wordLang_CodeBufferWrite (f r1) (f r2)) /\
   (apply_colour f (wordLang_DataBufferWrite r1 r2) =
     wordLang_DataBufferWrite (f r1) (f r2)) /\
   (apply_colour f (wordLang_FFI ffi_index ptr1 len1 ptr2 len2
     numset) =
     wordLang_FFI ffi_index (f ptr1) (f len1) (f ptr2) (f len2)
       (apply_nummaps_key f numset)) /\
   (apply_colour f (wordLang_LocValue r l1) =
     wordLang_LocValue (f r) l1) /\
   (apply_colour f (wordLang_Alloc num numset) =
     wordLang_Alloc (f num) (apply_nummaps_key f numset)) /\
   (apply_colour f (wordLang_StoreConsts a b c d ws) =
     wordLang_StoreConsts (f a) (f b) (f c) (f d) ws) /\
   (apply_colour f (wordLang_Raise num) = wordLang_Raise (f num)) /\
   (apply_colour f (wordLang_Return num1 nums) = wordLang_Return (f
     num1) (MAP f nums)) /\
   (apply_colour f wordLang_Tick = wordLang_Tick) /\
   (apply_colour f (reg_alloc_Set n wordLang_exp) = reg_alloc_Set n
     (apply_colour_exp f wordLang_exp)) /\
   (apply_colour f (wordLang_OpCurrHeap b n1 n2) =
     wordLang_OpCurrHeap b (f n1) (f n2)) /\
   (apply_colour f (wordLang_ShareInst ast_op semanticPrimitives_v
     wordLang_exp) = wordLang_ShareInst ast_op (f semanticPrimitives_v)
     (apply_colour_exp f wordLang_exp)) /\
   (apply_colour f (wordLang_Loop names body exit_names) =
     wordLang_Loop (apply_nummap_key f names) (apply_colour f body)
       (apply_nummap_key f exit_names)) /\
   (apply_colour f p = p)`;;


(* Liveness Analysis*)

(*Writes made by any inst as a sptree*)
let get_writes_inst_def = cake_define
  `get_writes_inst inst =
        match inst with
          (wordLang_Const asm_reg w) -> sptree_insert asm_reg one LN
        | (asm_Arith (asm_Binop bop r1 r2 ri)) -> sptree_insert r1
          one LN
        | (asm_Arith (wordLang_Shift (backend_common_word_shift) r1
          r2 ri)) -> sptree_insert r1 one LN
        | (asm_Arith (asm_Div r1 r2 r3)) -> sptree_insert r1 one LN
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) -> sptree_insert r4
          one (sptree_insert r1 one LN)
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) -> sptree_insert
          r4 one (sptree_insert r1 one LN)
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) -> sptree_insert
          r4 one (sptree_insert r1 one LN)
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) -> sptree_insert r2
          one (sptree_insert r1 one LN)
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> sptree_insert
          r2 one (sptree_insert r1 one LN)
        | (asm_Mem wordLang_Load r (Addr a w)) -> sptree_insert r one
          LN
        | (asm_Mem asm_Load32 r (Addr a w)) -> sptree_insert r one LN
        | (asm_Mem asm_Load8 r (Addr a w)) -> sptree_insert r one LN
        | (asm_FP (FPLess r f1 f2)) -> sptree_insert r one LN
        | (asm_FP (FPLessEqual r f1 f2)) -> sptree_insert r one LN
        | (asm_FP (FPEqual r f1 f2)) -> sptree_insert r one LN
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       if dimindex (:'a) = 64 then sptree_insert r1 one LN else
         sptree_insert r2 one (sptree_insert r1 one LN)
        | asm_inst -> LN`;;

(*Liveness for instructions, follows liveness equations
  live-sets are num_sets a.k.a. unit-sptrees*)
let get_live_inst_def = cake_define
  `get_live_inst x live =
        match x with
          wordLang_Skip -> live
        | (wordLang_Const asm_reg w) -> sptree_delete asm_reg live
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       match ri with Reg r3 -> sptree_insert r2 one (sptree_insert r3
         one (sptree_delete r1 live)) | _5 -> sptree_insert r2 one
         (sptree_delete r1 live)
        | (asm_Arith (wordLang_Shift (backend_common_word_shift) r1
          r2 ri)) ->
       match ri with Reg r3 -> sptree_insert r2 one (sptree_insert r3
         one (sptree_delete r1 live)) | _6 -> sptree_insert r2 one
         (sptree_delete r1 live)
        | (asm_Arith (asm_Div r1 r2 r3)) ->
       (sptree_insert r3 one (sptree_insert r2 one (sptree_delete r1
         live)))
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
       sptree_insert r4 one (sptree_insert r3 one (sptree_insert r2
         one (sptree_delete r1 live)))
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) ->
       sptree_insert r3 one (sptree_insert r2 one (sptree_delete r4
         (sptree_delete r1 live)))
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) ->
       sptree_insert r3 one (sptree_insert r2 one (sptree_delete r4
         (sptree_delete r1 live)))
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) ->
       sptree_insert r4 one (sptree_insert r3 one (sptree_delete r2
         (sptree_delete r1 live)))
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) ->
       sptree_insert r5 one (sptree_insert r4 one (sptree_insert r3
         one (sptree_delete r2 (sptree_delete r1 live))))
        | (asm_Mem wordLang_Load r (Addr a w)) ->
       sptree_insert a one (sptree_delete r live)
        | (asm_Mem wordLang_Store r (Addr a w)) ->
       sptree_insert a one (sptree_insert r one live)
        | (asm_Mem asm_Load32 r (Addr a w)) ->
       sptree_insert a one (sptree_delete r live)
        | (asm_Mem asm_Store32 r (Addr a w)) ->
       sptree_insert a one (sptree_insert r one live)
        | (asm_Mem asm_Load8 r (Addr a w)) ->
       sptree_insert a one (sptree_delete r live)
        | (asm_Mem asm_Store8 r (Addr a w)) ->
       sptree_insert a one (sptree_insert r one live)
        | (asm_FP (FPLess r f1 f2)) -> sptree_delete r live
        | (asm_FP (FPLessEqual r f1 f2)) -> sptree_delete r live
        | (asm_FP (FPEqual r f1 f2)) -> sptree_delete r live
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       if dimindex (:'a) = 64 then sptree_delete r1 live else
         sptree_delete r1 (sptree_delete r2 live)
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       if dimindex (:'a) = 64 then sptree_insert r1 one live else
         sptree_insert r2 one (sptree_insert r1 one live)
        | x -> live`;;

let big_union_def = cake_define
  `big_union ls = ITLIST (\x y. sptree_union x y) ls LN`;;

let get_live_exp_def = cake_define
  `get_live_exp expr =
        match expr with
          (wordLang_Var num) -> sptree_insert num one LN
        | (wordLang_Load wordLang_exp) -> get_live_exp wordLang_exp
        | (wordLang_Op wop ls) ->
       big_union (MAP get_live_exp ls)
        | (wordLang_Shift sh wordLang_exp nexp) -> sptree_union
          (get_live_exp wordLang_exp) (get_live_exp nexp)
        | expr -> LN`;;

let numset_list_insert_def = cake_define
  `(word_alloc_numset_list_insert [] t = t) /\
   (word_alloc_numset_list_insert (x :: xs) t = sptree_insert x
     one (word_alloc_numset_list_insert xs t))`;;

let get_live_def = cake_define
  `get_live x1 live lt =
        match x1 with
          wordLang_Skip -> live
        | (wordLang_Move pri ls) ->
       let killed = ITLIST sptree_delete (MAP FST ls) live in
         word_alloc_numset_list_insert (MAP SND ls) killed
        | (wordLang_Inst i) -> get_live_inst i live
        | (wordLang_Assign num wordLang_exp) ->
       let sub = get_live_exp wordLang_exp in
         sptree_union sub (sptree_delete num live)
        | (wordLang_Get num store) -> sptree_delete num live
        | (wordLang_Store wordLang_exp num) ->
       sptree_insert num one (sptree_union (get_live_exp
         wordLang_exp) live)
        | (linear_scan_Seq s1 s2) ->
       get_live s1 (get_live s2 live lt) lt
        | (wordLang_MustTerminate s1) ->
       get_live s1 live lt
        | (wordLang_If cmp r1 ri e2 e3) ->
       let e2_live = get_live e2 live lt in
       let e3_live = get_live e3 live lt in
       let union_live = sptree_union e2_live e3_live in
          match ri with Reg r2 -> sptree_insert r2 one (sptree_insert
            r1 one union_live) | _7 -> sptree_insert r1 one union_live
        | (wordLang_Alloc num numset) -> sptree_insert num one
          (sptree_union (FST numset) (SND numset))
        | (wordLang_StoreConsts a b c d ws) ->
       sptree_insert c one (sptree_insert d one (sptree_delete a
         (sptree_delete b live)))
        | (wordLang_Install r1 r2 r3 r4 numset) ->
       list_insert [r1; r2; r3; r4] (sptree_union (FST numset) (SND
         numset))
        | (wordLang_CodeBufferWrite r1 r2) ->
       list_insert [r1; r2] live
        | (wordLang_DataBufferWrite r1 r2) ->
       list_insert [r1; r2] live
        | (wordLang_FFI ffi_index ptr1 len1 ptr2 len2 numset) ->
      sptree_insert ptr1 one (sptree_insert len1 one
        (sptree_insert ptr2 one (sptree_insert len2 one (sptree_union
          (FST numset) (SND numset)))))
        | (wordLang_StoreConsts a b c d ws) ->
        (sptree_insert c one (sptree_insert d one live))
        | (wordLang_Raise num) -> sptree_insert num one live
        | (wordLang_Return num1 nums) -> sptree_insert num1 one
          (word_alloc_numset_list_insert nums live)
        | wordLang_Tick -> live
        | (wordLang_LocValue r l1) -> sptree_delete r live
        | (reg_alloc_Set n wordLang_exp) -> sptree_union
          (get_live_exp wordLang_exp) live
        | (wordLang_OpCurrHeap b n1 n2) -> sptree_insert n2 one
          (sptree_delete n1 live)
        | (wordLang_ShareInst mop semanticPrimitives_v wordLang_exp)
          ->
       let sub = get_live_exp wordLang_exp in
         if mop = wordLang_Store \/ mop = asm_Store8 \/ mop =
           asm_Store16 \/ mop = asm_Store32 then sptree_union sub
           (sptree_insert semanticPrimitives_v one live) else
           sptree_union sub (sptree_delete semanticPrimitives_v live)
        | (wordLang_Loop names body exit_names) -> names
        | (wordLang_Break n) ->
       match oEL n lt with
         NONE -> LN | SOME (names,exit_names) -> exit_names
        | (wordLang_Continue n) ->
       match oEL n lt with
         NONE -> LN | SOME (names,exit_names) -> names
        | (wordLang_Call NONE dest args h) ->
          word_alloc_numset_list_insert args LN
        | (wordLang_Call (SOME (_8,cutset,_9)) dest args h) ->
       sptree_union (sptree_union (FST cutset) (SND cutset))
         (word_alloc_numset_list_insert args LN)`;;

(* Dead instruction removal *)
let remove_dead_inst_def = cake_define
  `remove_dead_inst x live =
        match (x,live) with
          (wordLang_Skip,(live:one spt)) -> T
        | ((wordLang_Const asm_reg w),live) -> (sptree_lookup asm_reg
          live = NONE)
        | ((asm_Arith (asm_Binop bop r1 r2 ri)),live) ->
          (sptree_lookup r1 live = NONE)
        | ((asm_Arith (wordLang_Shift (backend_common_word_shift) r1
          r2 n)),live) -> (sptree_lookup r1 live = NONE)
        | ((asm_Arith (asm_Div r1 r2 r3)),live) -> (sptree_lookup r1
          live = NONE)
        | ((asm_Arith (asm_AddCarry r1 r2 r3 r4)),live) ->
       (sptree_lookup r1 live = NONE /\ sptree_lookup r4 live = NONE)
        | ((asm_Arith (asm_AddOverflow r1 r2 r3 r4)),live) ->
       (sptree_lookup r1 live = NONE /\ sptree_lookup r4 live = NONE)
        | ((asm_Arith (asm_SubOverflow r1 r2 r3 r4)),live) ->
       (sptree_lookup r1 live = NONE /\ sptree_lookup r4 live = NONE)
        | ((asm_Arith (asm_LongMul r1 r2 r3 r4)),live) ->
       (sptree_lookup r1 live = NONE /\ sptree_lookup r2 live = NONE)
        | ((asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)),live) ->
       (sptree_lookup r1 live = NONE /\ sptree_lookup r2 live = NONE)
        | ((asm_Mem wordLang_Load r (Addr a w)),live) ->
          (sptree_lookup r live = NONE)
        | ((asm_Mem asm_Load32 r (Addr a w)),live) -> (sptree_lookup
          r live = NONE)
        | ((asm_Mem asm_Load8 r (Addr a w)),live) -> (sptree_lookup r
          live = NONE)
        | ((asm_FP (FPLess r f1 f2)),live) -> (sptree_lookup r live =
          NONE)
        | ((asm_FP (FPLessEqual r f1 f2)),live) -> (sptree_lookup r
          live = NONE)
        | ((asm_FP (FPEqual r f1 f2)),live) -> (sptree_lookup r live
          = NONE)
        | ((asm_FP (FPMovToReg r1 r2 d):'a asm_inst),live) ->
       if dimindex (:'a) = 64 then sptree_lookup r1 live = NONE else
         (sptree_lookup r1 live = NONE /\ (sptree_lookup r2 live =
         NONE))
        | (x,live) -> F`;;

(* Delete dead code, w.r.t. a set of live variables.
  The liveset is a tuple (live,nlive):
  - live is an sptree of live variables
  - nlive is a list of globals which are NOT live

  This code is written assuming flat_exp_conventions,
    so many trivial cases are omitted.
*)
let remove_dead_def = cake_define
  `remove_dead prog live nlive lt =
        match prog with
          (wordLang_Move pri ls) ->
       let ls = FILTER (\(x,y). sptree_lookup x live = SOME one) ls
         in
       if ls = [] then (wordLang_Skip,live,nlive) else
       let killed = ITLIST sptree_delete (MAP FST ls) live in
         (wordLang_Move pri ls,word_alloc_numset_list_insert (MAP SND
           ls) killed,nlive)
        | (wordLang_Inst i) ->
       if remove_dead_inst i live then (wordLang_Skip,live,nlive)
         else (wordLang_Inst i,get_live_inst i live,nlive)
        | (wordLang_Get num store) ->
       if sptree_lookup num live = NONE then
         (wordLang_Skip,live,nlive) else (wordLang_Get num
           store,sptree_delete num live,FILTER (\s. ~(store = s)) nlive)
        | (wordLang_OpCurrHeap b num src) ->
       if sptree_lookup num live = NONE then
         (wordLang_Skip,live,nlive) else (
         wordLang_OpCurrHeap b num src,
           sptree_insert src one (sptree_delete num live),FILTER (\s.
             ~(CurrHeap = s)) nlive)
        | (wordLang_LocValue r l1) ->
       if sptree_lookup r live = NONE then
         (wordLang_Skip,live,nlive) else (wordLang_LocValue r
           l1,sptree_delete r live,nlive)
        | (reg_alloc_Set store_name wordLang_exp) ->
       match wordLang_exp with
         wordLang_Var r ->
         (if MEM store_name nlive then
           (wordLang_Skip,live,nlive) else
           (reg_alloc_Set store_name (wordLang_Var r),sptree_insert r
             one live,store_name :: nlive)) | _10 ->
         (let wordLang_prog = reg_alloc_Set store_name wordLang_exp
           in
           (wordLang_prog,get_live wordLang_prog live lt,[]))
        | (linear_scan_Seq s1 s2) ->
       let (s2,s2live,s2nlive) = remove_dead s2 live nlive lt in
       let (s1,s1live,s1nlive) = remove_dead s1 s2live s2nlive lt in
       let wordLang_prog =
         if s1 = wordLang_Skip then
           s2 else
           if s2 = wordLang_Skip then s1 else linear_scan_Seq s1 s2
             in (wordLang_prog,s1live,s1nlive)
        | (wordLang_MustTerminate s1) ->
       let (s1,s1live,s1nlive) = remove_dead s1 live nlive lt in
         (wordLang_MustTerminate s1,s1live,s1nlive)
        | (wordLang_If cmp r1 ri e2 e3) ->
       let (e2,e2_live,e2_nlive) = remove_dead e2 live nlive lt in
       let (e3,e3_live,e3_nlive) = remove_dead e3 live nlive lt in
       let union_live = sptree_union e2_live e3_live in
       let liveset =
          match ri with Reg r2 -> sptree_insert r2 one (sptree_insert
            r1 one union_live) | _11 -> sptree_insert r1 one union_live
            in
       let nliveset = FILTER (\s. MEM s e3_nlive) e2_nlive in
       let wordLang_prog =
         if e2 = wordLang_Skip /\ e3 = wordLang_Skip then
           wordLang_Skip else wordLang_If cmp r1 ri e2 e3 in
       (wordLang_prog,liveset,nliveset)
        | (wordLang_Call (SOME
          (semanticPrimitives_v,cutsets,ret_handler,l1,l2)) dest args h)
          ->
       let args_set = word_alloc_numset_list_insert args LN in
       let cutset = sptree_union (FST cutsets) (SND cutsets) in
       let live_set = sptree_union cutset args_set in
       let (ret_handler,_12) = remove_dead ret_handler live nlive lt
         in
       let h =
         (match h with
           NONE -> NONE | SOME (v',wordLang_prog,l1,l2) ->
           SOME (v',FST (remove_dead wordLang_prog live nlive
             lt),l1,l2)) in
       (wordLang_Call (SOME
         (semanticPrimitives_v,cutsets,ret_handler,l1,l2)) dest args
         h,(live_set,[]))
        | (wordLang_Call NONE a b c) ->
       let wordLang_prog = wordLang_Call NONE a b c in
         (wordLang_prog,get_live wordLang_prog live lt,[])
        | (wordLang_Alloc a b) ->
       let wordLang_prog = wordLang_Alloc a b in
         (wordLang_prog,get_live wordLang_prog live lt,[])
        | (wordLang_Raise a) ->
       let wordLang_prog = wordLang_Raise a in
         (wordLang_prog,get_live wordLang_prog live lt,[])
        | (wordLang_Return a b) ->
       let wordLang_prog = wordLang_Return a b in
         (wordLang_prog,get_live wordLang_prog live lt,[])
        | (wordLang_Loop names body exit_names) ->
       let lt' = (names,exit_names) :: lt in
       let (body',_13,_14) = remove_dead body names [] lt' in
       (wordLang_Loop names body' exit_names,names,[])
        | (wordLang_Break n) ->
       let wordLang_prog = wordLang_Break n in
         (wordLang_prog,get_live wordLang_prog live lt,[])
        | (wordLang_Continue n) ->
       let wordLang_prog = wordLang_Continue n in
         (wordLang_prog,get_live wordLang_prog live lt,[])
        | wordLang_prog -> (wordLang_prog,get_live wordLang_prog
          live lt,nlive)`;;

let remove_dead_prog_def = cake_define
  `remove_dead_prog wordLang_prog = FST (remove_dead wordLang_prog LN
  [] [])`;;

(*Single step immediate writes by a prog*)
let get_writes_def = cake_define
  `get_writes prog =
        match prog with
          (wordLang_Move pri ls) -> word_alloc_numset_list_insert
            (MAP FST ls) LN
        | (wordLang_Inst i) -> get_writes_inst i
        | (wordLang_Assign num wordLang_exp) -> sptree_insert num one
          LN
        | (wordLang_Get num store) -> sptree_insert num one LN
        | (wordLang_LocValue r l1) -> sptree_insert r one LN
        | (wordLang_Install r1 _15 _16 _17 _18) -> sptree_insert r1
          one LN
        | (wordLang_OpCurrHeap b r1 _19) -> sptree_insert r1 one LN
        | (wordLang_StoreConsts a b c d _20) -> sptree_insert a one
          (sptree_insert b one (sptree_insert c one (sptree_insert d one
          LN)))
        | (wordLang_ShareInst wordLang_Load semanticPrimitives_v _21)
          -> sptree_insert semanticPrimitives_v one LN
        | (wordLang_ShareInst asm_Load8 semanticPrimitives_v _22) ->
          sptree_insert semanticPrimitives_v one LN
        | (wordLang_ShareInst asm_Load16 semanticPrimitives_v _23) ->
          sptree_insert semanticPrimitives_v one LN
        | (wordLang_ShareInst asm_Load32 semanticPrimitives_v _24) ->
          sptree_insert semanticPrimitives_v one LN
        | wordLang_prog -> LN`;;

(* Old representation *)
(* Definition get_clash_sets_def:
  (get_clash_sets (Seq s1 s2) live =
    let (hd,ls) = get_clash_sets s2 live in
    let (hd',ls') = get_clash_sets s1 hd in
      (hd',(ls' ++ ls))) ∧
  (get_clash_sets (MustTerminate s1) live =
     get_clash_sets s1 live) ∧
  (get_clash_sets (If cmp r1 ri e2 e3) live =
    let (h2,ls2) = get_clash_sets e2 live in
    let (h3,ls3) = get_clash_sets e3 live in
    let union_live = union h2 h3 in
    let merged = case ri of Reg r2 => insert r2 () (insert r1 ()
      union_live)
                      | _ => insert r1 () union_live in
      (merged,ls2++ls3)) ∧
  (get_clash_sets (Call(SOME(v,cutset,ret_handler,l1,l2))dest args h)
    live =
    (*top level*)
    let args_set = numset_list_insert args LN in
    let (hd,ls) = get_clash_sets ret_handler live in
    (*Outer liveset*)
    let live_set = union cutset args_set in
    (*Returning clash set*)
    let ret_clash = insert v () cutset in
    (case h of
      NONE => (live_set,ret_clash::hd::ls)
    | SOME(v',prog,l1,l2) =>
        let (hd',ls') = get_clash_sets prog live in
        (*Handler clash set*)
        let h_clash = insert v' () cutset in
        (live_set,h_clash::ret_clash::hd::hd'::ls++ls'))) ∧
  (*Catchall for cases where we dont have in sub programs live sets*)
  (get_clash_sets prog live =
    let i_set = union (get_writes prog) live in
      (get_live prog live,[i_set]))
  End
*)

(* Potentially more efficient liveset representation for checking /
   allocation*)
let get_delta_inst_def = cake_define
  `get_delta_inst x =
        match x with
          wordLang_Skip -> reg_alloc_Delta [] []
        | (wordLang_Const asm_reg w) -> reg_alloc_Delta [asm_reg] []
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       match ri with Reg r3 -> reg_alloc_Delta [r1] [r2; r3] | _25 ->
         reg_alloc_Delta [r1] [r2]
        | (asm_Arith (wordLang_Shift (backend_common_word_shift) r1
          r2 ri)) ->
       match ri with Reg r3 -> reg_alloc_Delta [r1] [r2; r3] | _26 ->
         reg_alloc_Delta [r1] [r2]
        | (asm_Arith (asm_Div r1 r2 r3)) -> reg_alloc_Delta [r1] [r3;
          r2]
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) -> reg_alloc_Delta
          [r1; r4] [r4; r3; r2]
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) ->
          reg_alloc_Delta [r1; r4] [r3; r2]
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) ->
          reg_alloc_Delta [r1; r4] [r3; r2]
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) -> reg_alloc_Delta
          [r1; r2] [r4; r3]
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> reg_alloc_Delta
          [r1; r2] [r5; r4; r3]
        | (asm_Mem wordLang_Load r (Addr a w)) -> reg_alloc_Delta [r]
          [a]
        | (asm_Mem wordLang_Store r (Addr a w)) -> reg_alloc_Delta []
          [r; a]
        | (asm_Mem asm_Load32 r (Addr a w)) -> reg_alloc_Delta [r]
          [a]
        | (asm_Mem asm_Store32 r (Addr a w)) -> reg_alloc_Delta []
          [r; a]
        | (asm_Mem asm_Load8 r (Addr a w)) -> reg_alloc_Delta [r] [a]
        | (asm_Mem asm_Store8 r (Addr a w)) -> reg_alloc_Delta [] [r;
          a]
        | (asm_FP (FPLess r f1 f2)) -> reg_alloc_Delta [r] []
        | (asm_FP (FPLessEqual r f1 f2)) -> reg_alloc_Delta [r] []
        | (asm_FP (FPEqual r f1 f2)) -> reg_alloc_Delta [r] []
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       if dimindex (:'a) = 64 then reg_alloc_Delta [r1] [] else
         reg_alloc_Delta [r1; r2] []
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       if dimindex (:'a) = 64 then reg_alloc_Delta [] [r1] else
         reg_alloc_Delta [] [r1; r2]
        | x -> reg_alloc_Delta [] []`;;

let get_reads_exp_def = cake_define
  `get_reads_exp expr =
        match expr with
          (wordLang_Var num) -> [num]
        | (wordLang_Load wordLang_exp) -> get_reads_exp wordLang_exp
        | (wordLang_Op wop ls) ->
         FLAT (MAP get_reads_exp ls)
        | (wordLang_Shift sh wordLang_exp nexp) -> get_reads_exp
          wordLang_exp ++ get_reads_exp nexp
        | expr -> []`;;

let get_clash_tree_def = cake_define
  `(get_clash_tree wordLang_Skip lt = reg_alloc_Delta [] []) /\
   (get_clash_tree (wordLang_Move pri ls) lt =
     reg_alloc_Delta (MAP FST ls) (MAP SND ls)) /\
   (get_clash_tree (wordLang_Inst i) lt = get_delta_inst i) /\
   (get_clash_tree (wordLang_Assign num' wordLang_exp) lt =
     reg_alloc_Delta [num'] (get_reads_exp wordLang_exp)) /\
   (get_clash_tree (wordLang_Get num' store) lt = reg_alloc_Delta
     [num'] []) /\
   (get_clash_tree (wordLang_Store wordLang_exp num') lt =
     reg_alloc_Delta [] (num' :: get_reads_exp wordLang_exp)) /\
   (get_clash_tree (linear_scan_Seq s1 s2) lt = linear_scan_Seq
     (get_clash_tree s1 lt) (get_clash_tree s2 lt)) /\
   (get_clash_tree (wordLang_If cmp r1 ri e2 e3) lt =
     (let e2t = get_clash_tree e2 lt in
     let e3t = get_clash_tree e3 lt in
     match ri with
       Reg r2 -> linear_scan_Seq (reg_alloc_Delta [] [r1; r2])
         (linear_scan_Branch NONE e2t e3t) | _27 -> linear_scan_Seq
         (reg_alloc_Delta [] [r1]) (linear_scan_Branch NONE e2t e3t)))
         /\
   (get_clash_tree (wordLang_MustTerminate s) lt =
     get_clash_tree s lt) /\
   (get_clash_tree (wordLang_Alloc num' numset) lt =
     linear_scan_Seq (reg_alloc_Delta [] [num']) (reg_alloc_Set
       (sptree_union (FST numset) (SND numset)))) /\
   (get_clash_tree (wordLang_Install r1 r2 r3 r4 numset) lt =
     linear_scan_Seq (reg_alloc_Delta [] [r4; r3; r2; r1])
       (linear_scan_Seq (reg_alloc_Set (sptree_union (FST numset) (SND
       numset))) (reg_alloc_Delta [r1] []))) /\
   (get_clash_tree (wordLang_CodeBufferWrite r1 r2) lt =
     reg_alloc_Delta [] [r2; r1]) /\
   (get_clash_tree (wordLang_DataBufferWrite r1 r2) lt =
     reg_alloc_Delta [] [r2; r1]) /\
   (get_clash_tree (wordLang_FFI ffi_index ptr1 len1 ptr2 len2
     numset) lt =
     linear_scan_Seq (reg_alloc_Delta [] [ptr1; len1; ptr2; len2])
       (reg_alloc_Set (sptree_union (FST numset) (SND numset)))) /\
   (get_clash_tree (wordLang_Raise num') lt = reg_alloc_Delta []
     [num']) /\
   (get_clash_tree (wordLang_Return num1 nums) lt = reg_alloc_Delta
     [] (num1 :: nums)) /\
   (get_clash_tree wordLang_Tick lt = reg_alloc_Delta [] []) /\
   (get_clash_tree (wordLang_LocValue r l1) lt = reg_alloc_Delta [r]
     []) /\
   (get_clash_tree (reg_alloc_Set n wordLang_exp) lt =
     reg_alloc_Delta [] (get_reads_exp wordLang_exp)) /\
   (get_clash_tree (wordLang_OpCurrHeap b dst src) lt =
     reg_alloc_Delta [dst] [src]) /\
   (get_clash_tree (wordLang_StoreConsts a b c d ws) lt =
     reg_alloc_Delta [a; b; c; d] [c; d]) /\
   (get_clash_tree (wordLang_ShareInst ast_op semanticPrimitives_v
     wordLang_exp) lt = (if ast_op = wordLang_Store \/ ast_op =
     asm_Store8 \/ ast_op = asm_Store16 \/ ast_op = asm_Store32 then
     reg_alloc_Delta [] (semanticPrimitives_v :: get_reads_exp
     wordLang_exp) else reg_alloc_Delta [semanticPrimitives_v]
     (get_reads_exp wordLang_exp))) /\
   (get_clash_tree (wordLang_Loop names body exit_names) lt =
     linear_scan_Seq (reg_alloc_Set names)
       (linear_scan_Seq (reg_alloc_Set exit_names)
         (linear_scan_Seq (get_clash_tree body ((names,exit_names) ::
           lt))
           (reg_alloc_Set names)))) /\
   (get_clash_tree (wordLang_Break n) lt =
     (match oEL n lt with
       NONE -> reg_alloc_Set LN | SOME (names,exit_names) ->
         reg_alloc_Set exit_names)) /\
   (get_clash_tree (wordLang_Continue n) lt =
     (match oEL n lt with
       NONE -> reg_alloc_Set LN | SOME (names,exit_names) ->
         reg_alloc_Set names)) /\
   (get_clash_tree (wordLang_Call ret dest args h) lt =
     (let args_set = word_alloc_numset_list_insert args LN in
     match ret with
       NONE -> reg_alloc_Set args_set | SOME
         (vs,cutsets,ret_handler,_28,_29) ->
       (let cutset = sptree_union (FST cutsets) (SND cutsets) in
       let live_set = sptree_union cutset args_set in
       let ret_tree = linear_scan_Seq (reg_alloc_Set
         (word_alloc_numset_list_insert vs cutset)) (get_clash_tree
         ret_handler lt) in
       match h with
         NONE -> linear_scan_Seq (reg_alloc_Set live_set) ret_tree |
           SOME (v',wordLang_prog,_30,_31) ->
         (let handler_tree =
           linear_scan_Seq (reg_alloc_Set (sptree_insert v' one
             cutset)) (get_clash_tree wordLang_prog lt) in
         linear_scan_Branch (SOME live_set) ret_tree
           handler_tree))))`;;

(* Preference edges
  The allocator tries hard to coalesce these edges
*)
let get_prefs_def = cake_define
  `get_prefs prog acc =
        match prog with
          (wordLang_Move pri ls) -> (MAP (\(x,y). (pri,x,y)) ls) ++
            acc
        | (wordLang_MustTerminate s1) ->
       get_prefs s1 acc
        | (linear_scan_Seq s1 s2) ->
       get_prefs s1 (get_prefs s2 acc)
        | (wordLang_If cmp num rimm e2 e3) ->
       get_prefs e2 (get_prefs e3 acc)
        | (wordLang_Call (SOME
          (semanticPrimitives_v,cutset,ret_handler,l1,l2)) dest args h)
          ->
       match h with
         NONE -> get_prefs ret_handler acc | SOME
           (semanticPrimitives_v,wordLang_prog,l1,l2) -> get_prefs
           wordLang_prog (get_prefs ret_handler acc)
        | (wordLang_Loop names body exit_names) -> get_prefs body acc
        | wordLang_prog -> acc`;;

(*
  For each var, we collect 5 tuples indicating the number of
  instructions in which it is involved in:
    (lhs const,lhs reg,lhs memory, rhs reg, rhs memory)

  Currently, this just treats FP as a "reg" instruction

  This is meant to be small and quick to compute, because it has to be
    applied
  to the entire program just before register allocation, which can be
    huge.

*)

new_type_abbrev("heu_data",`: num#num#num#num#num`);;

let add1_lhs_const_def = cake_define
  `add1_lhs_const x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (1,0,0,0,0) t | SOME
       (const,asm_reg,mem,rreg,rmem) ->
     sptree_insert x (const + 1,asm_reg,mem,rreg,rmem) t)`;;

let add1_lhs_reg_def = cake_define
  `add1_lhs_reg x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,1,0,0,0) t | SOME
       (const,asm_reg,mem,rreg,rmem) ->
     sptree_insert x (const,asm_reg + 1,mem,rreg,rmem) t)`;;

let add1_lhs_mem_def = cake_define
  `add1_lhs_mem x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,0,1,0,0) t | SOME
       (const,asm_reg,mem,rreg,rmem) ->
     sptree_insert x (const,asm_reg,mem + 1,rreg,rmem) t)`;;

let add1_rhs_reg_def = cake_define
  `add1_rhs_reg x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,0,0,1,0) t | SOME
       (const,asm_reg,mem,rreg,rmem) ->
     sptree_insert x (const,asm_reg,mem,rreg + 1,rmem) t)`;;

let add1_rhs_mem_def = cake_define
  `add1_rhs_mem x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,0,0,0,1) t | SOME
       (const,asm_reg,mem,rreg,rmem) ->
     sptree_insert x (const,asm_reg,mem,rreg,rmem + 1) t)`;;

let get_heu_inst_def = cake_define
  `get_heu_inst x tup =
        match x with
          wordLang_Skip -> tup
        | (wordLang_Const asm_reg w) ->
       (add1_lhs_const asm_reg tup)
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       (match ri with
         Reg r3 ->
           (add1_lhs_reg r1
           (add1_rhs_reg r3 (add1_rhs_reg r2 tup))) | _32 ->
           (add1_lhs_reg r1
           (add1_rhs_reg r2 tup)))
        | (asm_Arith (wordLang_Shift (backend_common_word_shift) r1
          r2 ri)) ->
       (match ri with
         Reg r3 ->
           (add1_lhs_reg r1
           (add1_rhs_reg r3 (add1_rhs_reg r2 tup))) | _33 ->
           (add1_lhs_reg r1
           (add1_rhs_reg r2 tup)))
        | (asm_Arith (asm_Div r1 r2 r3)) ->
        (add1_lhs_reg r1
        (add1_rhs_reg r3 (add1_rhs_reg r2 tup)))
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
        (add1_lhs_reg r4 (add1_lhs_reg r1
        (add1_rhs_reg r4 (add1_rhs_reg r3 (add1_rhs_reg r2 tup)))))
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) ->
        (add1_lhs_reg r4 (add1_lhs_reg r1
        (add1_rhs_reg r3 (add1_rhs_reg r2 tup))))
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) ->
        (add1_lhs_reg r4 (add1_lhs_reg r1
        (add1_rhs_reg r3 (add1_rhs_reg r2 tup))))
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) ->
        (add1_lhs_reg r2 (add1_lhs_reg r1
        (add1_rhs_reg r4 (add1_rhs_reg r3 tup))))
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) ->
        (add1_lhs_reg r2 (add1_lhs_reg r1
        (add1_rhs_reg r5 (add1_rhs_reg r4 (add1_rhs_reg r3 tup)))))
        | (asm_Mem wordLang_Load r (Addr a w)) ->
        (add1_lhs_mem r tup)
        | (asm_Mem wordLang_Store r (Addr a w)) ->
        (add1_rhs_mem r tup)
        | (asm_Mem asm_Load32 r (Addr a w)) ->
        (add1_lhs_mem r tup)
        | (asm_Mem asm_Load8 r (Addr a w)) ->
        (add1_lhs_mem r tup)
        | (asm_Mem asm_Store32 r (Addr a w)) ->
        (add1_rhs_mem r tup)
        | (asm_Mem asm_Store8 r (Addr a w)) ->
        (add1_rhs_mem r tup)
        | (asm_FP (FPLess r f1 f2)) ->
        (add1_lhs_reg r tup)
        | (asm_FP (FPLessEqual r f1 f2)) ->
        (add1_lhs_reg r tup)
        | (asm_FP (FPEqual r f1 f2)) ->
        (add1_lhs_reg r tup)
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
        (add1_lhs_reg r2 (add1_lhs_reg r1 tup))
        | (asm_FP (FPMovFromReg d r1 r2)) ->
        (add1_rhs_reg r2 (add1_rhs_reg r1 tup))
        | x -> tup`;;

(* For Ifs, as a heuristic we take the max over branching paths *)
let heu_max_def = cake_define
  `heu_max (c1,r1,m1,rr1,rm1) (c2,r2,m2,rr2,rm2) =
     (MAX c1 c2,MAX r1 r2,MAX m1 m2,MAX rr1 rr2,MAX rm1 rm2)`;;

let heu_max_all_def = cake_define
  `heu_max_all t1 t2 =
   (let t1r = difference t1 t2 in
   sptree_union
   t1r
   (mllist_mapi (\k semanticPrimitives_v.
     match sptree_lookup k t1 with
       NONE -> semanticPrimitives_v | SOME v' -> heu_max
         semanticPrimitives_v v') t2))`;;

let heu_merge_call_def = cake_define
  `heu_merge_call (t1:one spt) t2 =
   sptree_union t1 t2`;;

(* We use "lr" to approximate any new vars not already tracked in calls
   *)
let add_call_def = cake_define
  `(add_call lr calls':one spt) =
   sptree_union (sptree_map (\semanticPrimitives_v. one) lr)
     calls'`;;

let get_heu_def = cake_define
  `get_heu fc f lr =
        match (f,lr) with
          ((wordLang_Move pri ls),(lr,calls)) ->
       (ITLIST add1_lhs_reg
       (MAP FST ls)
       (ITLIST add1_rhs_reg (MAP SND ls) lr),calls)
        | ((wordLang_Inst i),(lr,calls)) -> (get_heu_inst i lr,calls)
        | ((wordLang_Get num store),(lr,calls)) ->
       (add1_lhs_mem num lr,calls)
        | ((reg_alloc_Set _34 wordLang_exp),(lr,calls)) ->
       (match wordLang_exp with (wordLang_Var r) ->
          (add1_rhs_mem r lr,calls) | _35 -> (lr,calls))
        | ((wordLang_OpCurrHeap b dst src),(lr,calls)) ->
       (add1_lhs_reg dst (add1_rhs_reg src lr),calls)
        | ((wordLang_LocValue r l1),(lr,calls)) ->
       (add1_lhs_reg r lr,calls)
        | ((linear_scan_Seq s1 s2),lr) -> get_heu fc s2 (get_heu fc
          s1 lr)
        | ((wordLang_MustTerminate s1),lr) -> get_heu fc s1 lr
        | ((wordLang_If cmp r1 ri e2 e3),lr) ->
       let (lr2,calls2) = get_heu fc e2 lr in
       let (lr3,calls3) = get_heu fc e3 lr in
       let lr = heu_max_all lr2 lr3 in
       let calls = heu_merge_call (calls2:one spt) calls3 in
       ((match ri with
         Reg r2 -> add1_rhs_reg r1 (add1_rhs_reg r2 lr) | _36 ->
         add1_rhs_reg r1 lr),calls)
        | ((wordLang_Call NONE dest args h),(lr,calls)) ->
       match dest with
         NONE -> (lr,calls) | SOME p ->
         (if p = fc then (lr,add_call lr calls) else (lr,calls))
        | ((wordLang_Call (SOME (_37,_38,e2,_39,_40)) dest args
          h),(lr,calls)) ->
       let calls =
         match dest with NONE -> calls | SOME p ->
           (if p = fc then (add_call lr calls) else calls) in
       let (lr2,calls2) = (get_heu fc e2 (lr,calls)) in
       match h with
         NONE -> (lr2,calls) | SOME (_41,e3,_42,_43) ->
         (let (lr3,calls3) = get_heu fc e3 (lr,calls) in
         (heu_max_all lr2 lr3,heu_merge_call calls2 calls3))
        | ((wordLang_ShareInst wordLang_Load r _44),(lr,calls)) ->
          (add1_lhs_mem r lr,calls)
        | ((wordLang_ShareInst asm_Load8 r _45),(lr,calls)) ->
          (add1_lhs_mem r lr,calls)
        | ((wordLang_ShareInst asm_Load16 r _46),(lr,calls)) ->
          (add1_lhs_mem r lr,calls)
        | ((wordLang_ShareInst asm_Load32 r _47),(lr,calls)) ->
          (add1_lhs_mem r lr,calls)
        | ((wordLang_ShareInst wordLang_Store r _48),(lr,calls)) ->
          (add1_rhs_mem r lr,calls)
        | ((wordLang_ShareInst asm_Store8 r _49),(lr,calls)) ->
          (add1_rhs_mem r lr,calls)
        | ((wordLang_ShareInst asm_Store16 r _50),(lr,calls)) ->
          (add1_rhs_mem r lr,calls)
        | ((wordLang_ShareInst asm_Store32 r _51),(lr,calls)) ->
          (add1_rhs_mem r lr,calls)
        | ((wordLang_Loop names body exit_names),lr) -> get_heu fc
          body lr
        | (f,lrc) -> lrc`;;

(* Forced edges for certain instructions *)
let get_forced_def = cake_define
  `get_forced c prog acc =
        match (c,prog) with
          ((c:'a asm_config),((wordLang_Inst i):'a wordLang_prog)) ->
       match i with
         asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
          (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
            then
             (if r1 = r3 then [] else [(r1,r3)]) ++
             (if r1 = r4 then [] else [(r1,r4)]) ++
             acc else acc) | asm_Arith (asm_AddOverflow r1 r2 r3 r4)
               ->
          (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
            then
             (if r1 = r3 then [] else [(r1,r3)]) ++
             acc else acc) | asm_Arith (asm_SubOverflow r1 r2 r3 r4)
               ->
          (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
            then
             (if r1 = r3 then [] else [(r1,r3)]) ++
             acc else acc) | asm_Arith (asm_LongMul r1 r2 r3 r4) ->
          (if (asm_config_ISA c = ARMv7) then
            (if (r1 = r2) then [] else [(r1,r2)]) ++ acc else if
              (asm_config_ISA c = ARMv8) \/ (asm_config_ISA c = RISC_V)
              \/ (asm_config_ISA c = Ag32) then
            (if r1 = r3 then [] else [(r1,r3)]) ++
            (if r1 = r4 then [] else [(r1,r4)]) ++
            acc else
            acc) | asm_FP (FPMovToReg r1 r2 d) ->
           (if dimindex (:'a) = 32 /\ ~(r1 = r2) then [(r1,r2)] else
             []) ++ acc | asm_FP (FPMovFromReg d r1 r2) ->
           (if dimindex (:'a) = 32 /\ ~(r1 = r2) then [(r1,r2)] else
             []) ++ acc | _52 -> acc
        | (c,(wordLang_MustTerminate s1)) ->
       get_forced c s1 acc
        | (c,(linear_scan_Seq s1 s2)) ->
       get_forced c s1 (get_forced c s2 acc)
        | (c,(wordLang_If cmp num rimm e2 e3)) ->
       get_forced c e2 (get_forced c e3 acc)
        | (c,(wordLang_Call (SOME
          (semanticPrimitives_v,cutset,ret_handler,l1,l2)) dest args h))
          ->
       match h with
         NONE -> get_forced c ret_handler acc | SOME
           (semanticPrimitives_v,wordLang_prog,l1,l2) -> get_forced c
           wordLang_prog (get_forced c ret_handler acc)
        | (c,(wordLang_Loop names body exit_names)) -> get_forced c
          body acc
        | (c,wordLang_prog) -> acc`;;

(*col is injective over every cut set*)
let check_colouring_ok_alt_def = cake_define
  `(check_colouring_ok_alt col [] = T) /\
   (check_colouring_ok_alt col (x :: xs) <=>
     (let names = MAP (col o FST) (toAList x) in
       ALL_DISTINCT names /\ check_colouring_ok_alt col xs))`;;

let every_even_colour_def = cake_define
  `every_even_colour col <=>
   EVERY (\(x,y). if is_phy_var x then y = x DIV 2 else T)
     (toAList col)`;;

(*Extract a colouring function from the generated sptree*)
let total_colour_def = cake_define
  `total_colour col x =
     (match sptree_lookup x col with NONE -> (if is_phy_var x then
       x else 0) | SOME x -> 2 * x)`;;

(*Check that the oracle provided colour (if it exists) is okay*)
let oracle_colour_ok_def = cake_define
  `oracle_colour_ok k col_opt tree wordLang_prog ls <=>
   (match col_opt with
     NONE -> NONE | SOME col ->
      (let tcol = total_colour col in
      if (every_even_colour col /\ ~(check_clash_tree tcol tree LN LN
        = NONE)) then
        let wordLang_prog = apply_colour tcol wordLang_prog in
        if
          every_stack_var (\x. x >= 2 * k) wordLang_prog /\
          EVERY (\(x,y). ~((tcol x) = (tcol y))) ls then
          SOME wordLang_prog else
          NONE else NONE))`;;

(* Returns
  1) a lookup table
    v -> "spill cost"
  2) the move list, with associated priorities

  For now, the spill cost metric is just 6 magic numbers
*)
(*
  Canonize by flipping moves (all move x<=y)
  Filter some obviously impossible ones out
  Then SORT them by lexicographic order, and count
  returns (num, maxpriority, (x,y))
*)
let canonize_moves_aux_def = cake_define
  `(canonize_moves_aux curp curm ctr [] acc = (ctr,curp,curm) :: acc) /\
   (canonize_moves_aux curp curm ctr ((p,m) :: xs) acc =
     (if curm = m then
       canonize_moves_aux (MAX curp p) m (ctr + 1) xs acc else
       canonize_moves_aux p m 1 xs ((ctr,curp,curm) :: acc)))`;;

let canonize_moves_def = cake_define
  `canonize_moves ls =
   (let can1 = MAP (\((p:num),((x:num),(y:num))). if (x <= y) then
     (p,(x,y)) else (p,(y,x))) ls in
   let can2 = sort
     (\(p1,(x1,y1)) (p2,(x2,y2)).
       if x1 = x2 then
         if y1 = y2 then
           p1 < p2 else y1 < y2 else x1 < x2) can1 in
   match can2 with [] -> [] | ((p,m) :: xs) -> canonize_moves_aux
     p m 1 xs [])`;;

(* TODO: ALL of these magic numbers must be adjusted!! *)

let get_spillcost_def = cake_define
  `get_spillcost (c,lr,lm,rr,rm) istail =
   (c + 2 * lr + 4 * lm + 2 * rr + 4 * rm) *
   (if istail then 5 else 1)`;;

(*
  Prioritize moves that happen a lot, and have high max priority
  also give some weight to the spill cost of their endpoints
*)
let get_coalescecost_def = cake_define
  `get_coalescecost spillcost (n,p,(x,y)) =
   (let xcost = if sptree_lookup x spillcost = NONE then 0 else 1 in
   let ycost = if sptree_lookup y spillcost = NONE then 0 else 1 in
   (n * (10 * (p + 1) + xcost + ycost),(x,y)))`;;

let get_heuristics_def = cake_define
  `get_heuristics alg fc wordLang_prog =
   (if alg MOD 2 = 1 then
     let (lr,calls') = get_heu fc wordLang_prog (LN,LN) in
     let moves = get_prefs wordLang_prog [] in
     let spillcosts = mllist_mapi (\k semanticPrimitives_v.
       get_spillcost semanticPrimitives_v (sptree_lookup k calls' =
       NONE)) lr in
     let canon_moves = canonize_moves moves in
     let heu_moves = MAP (get_coalescecost spillcosts) canon_moves in
     (heu_moves,SOME spillcosts) else
     let moves = get_prefs wordLang_prog [] in
     (moves,NONE))`;;

let select_reg_alloc_def = cake_define
  `select_reg_alloc alg spillcosts k heu_moves tree forced fs =
     (if 4 <= alg then
       linear_scan_reg_alloc k heu_moves tree forced else
       reg_alloc (if alg <= 1 then reg_alloc_Simple else
         reg_alloc_IRC) spillcosts k heu_moves tree forced fs)`;;

(* For a move x <- y
  if x is a register, then y should not be forced stack
  else,
    if y is a stack variable or forced stack,
    then we mark x as forced stack as well
*)
let merge_stack_only_def = cake_define
  `merge_stack_only (x,y) (ts,fs) =
   (if sptree_lookup x ts = SOME one then
     let ts = if is_alloc_var y then sptree_insert y one ts else ts
       in
     let fs = if is_phy_var y then fs else sptree_insert x one fs in
     (ts,fs) else
     if is_stack_var x then
       let ts = if is_alloc_var y then sptree_insert y one ts else ts
         in
       (ts,fs) else
       (sptree_delete y ts,fs))`;;

let merge_stack_sets_def = cake_define
  `merge_stack_sets (ts,fs) (tsL,fsL) (tsR,fsR) =
   (let keep1 = inter tsR (inter tsL ts) in
   let keep2 = sptree_union (difference tsL ts) (difference tsR ts)
     in
     (sptree_union keep1 keep2,sptree_union fsL fsR))`;;

let remove_temp_stack_def = cake_define
  `remove_temp_stack ls (ts,fs) =
     (ITLIST sptree_delete ls ts,fs)`;;

(* Alloc variables that are already stack or
  only ever involved in stack moves *)
let get_stack_only_aux_def = cake_define
  `get_stack_only_aux tfs prog =
        match prog with
          (wordLang_Move pri ls) ->
       ITLIST merge_stack_only ls tfs
        | (linear_scan_Seq s1 s2) ->
       get_stack_only_aux (get_stack_only_aux tfs s2) s1
        | (wordLang_If cmp r1 ri e2 e3) ->
       let tfsL = get_stack_only_aux tfs e2 in
       let tfsR = get_stack_only_aux tfs e3 in
       let tfsM = merge_stack_sets tfs tfsL tfsR in
         match ri with
           Reg r2 -> remove_temp_stack [r1; r2] tfsM | _53 ->
             remove_temp_stack [r1] tfsM
        | (wordLang_MustTerminate s) ->
       get_stack_only_aux tfs s
        | (wordLang_Call ret dest args h) ->
       (match ret with
         NONE -> tfs | SOME
           (semanticPrimitives_v,cutset,ret_handler,_54,_55) ->
         (let rettfs = get_stack_only_aux tfs ret_handler in
         match h with
           NONE -> rettfs | SOME (v',handler,_56,_57) ->
           (let handlertfs =
             get_stack_only_aux tfs handler in
           merge_stack_sets tfs rettfs handlertfs)))
        | (wordLang_Loop names body exit_names) ->
       get_stack_only_aux tfs body
        | wordLang_prog ->
       match get_clash_tree wordLang_prog [] with
         reg_alloc_Delta ws rs -> remove_temp_stack (ws ++ rs) tfs
           | _58 -> tfs`;;

let get_stack_only_def = cake_define
  `get_stack_only wordLang_prog = SND (get_stack_only_aux (LN,LN)
  wordLang_prog)`;;

(*
  fc is the current prog number
  alg is the allocation algorithm,
    0: simple allocator, no spill heuristics
    1: simple allocator + spill heuristics
    2: IRC allocator, no spill heuristics (default)
    3: IRC allocator + spill heuristics
  >=4: linear scan register allocator
  k is the number of registers
  prog is the program to be colored
  col_opt is an optional oracle colour
*)
let word_alloc_def = cake_define
  `word_alloc fc c alg k wordLang_prog col_opt =
   (let tree = get_clash_tree wordLang_prog [] in
   let fs = get_stack_only wordLang_prog in
   let forced = get_forced c wordLang_prog [] in
   match oracle_colour_ok k col_opt tree wordLang_prog forced with
     NONE ->
       (let (heu_moves,spillcosts) = get_heuristics alg fc
         wordLang_prog in
       (match select_reg_alloc alg spillcosts k heu_moves tree forced
         fs with
         M_success col ->
           apply_colour (total_colour col) wordLang_prog | M_failure
             _59 -> wordLang_prog)) | SOME col_prog ->
       col_prog)`;;

(*The initial move, ssa and limit vars*)
let setup_ssa_def = cake_define
  `setup_ssa n lim (wordLang_prog:'a wordLang_prog) =
   (let args = even_list n in
   let (new_ls,ssa',n') = list_next_var_rename args LN lim in
     ((wordLang_Move 1) (ZIP (new_ls,args)),ssa',n'))`;;

let limit_var_def = cake_define
  `limit_var wordLang_prog =
     (let x = max_var wordLang_prog in
     x + (4 - (x MOD 4)) + 1)`;;

let full_ssa_cc_trans_def = cake_define
  `full_ssa_cc_trans n wordLang_prog =
     (let lim = limit_var wordLang_prog in
     let (mov,ssa,na) = setup_ssa n lim wordLang_prog in
     let (prog',ssa',na') = ssa_cc_trans wordLang_prog ssa na [] in
       linear_scan_Seq mov prog')`;;
