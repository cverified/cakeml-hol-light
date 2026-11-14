(* ======================================================== *)
(*  word_alloc: ported from HOL4's
    compiler/backend/word_allocScript.sml
    A definition theory, with 68 definitions and 4 theorems.  Needed
    by 7 files of the port.  *)
(* ======================================================== *)

(*
  This is the compiler's register allocator. It supports different modes:
      0) simple allocator, no spill heuristics;
      1) simple allocator + spill heuristics;
      2) IRC allocator, no spill heuristics (default);
      3) IRC allocator + spill heuristics;
      4) linear scan register allocator.
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
(* for arity-2 Const *)
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "word_alloc"
  ["asm"; "linear_scan"; "misc"; "mllist"; "reg_alloc"; "wordLang"];;

let _ = do_list hide_constant ["inst"];;

(* HOL4 word_allocScript.sml:19: the overload Move0, which the port
   expands *)
(* HOL4 word_allocScript.sml:20: the overload Move1, which the port
   expands *)

(*SSA form*)
let apply_nummap_key_def = new_definition
  `apply_nummap_key f names =
   fromAList (MAP (\(x,y). f x,y) (toAList names))`;;

let apply_nummaps_key_def = new_definition
  `apply_nummaps_key f names =
   (fromAList (MAP (\(x,y). f x,y) (toAList (FST names))),
    fromAList (MAP (\(x,y). f x,y) (toAList (SND names))))`;;

let option_lookup_def = new_definition
  `option_lookup t v = (match sptree_lookup v t with NONE -> 0 | SOME
  x -> x)`;;

let even_list_def = new_definition
  `(even_list = list_of_seq (\x. 2 * x))`;;

(*Consistently sets up the next alloc variable rename for v*)
let next_var_rename_def = new_definition
  `next_var_rename v ssa (na:num) = (na,sptree_insert v na ssa,na +
  4)`;;

let list_next_var_rename_def,list_next_var_rename_ind = define_rec
  [`list_next_var_rename [] ssa (na:num) = ([],ssa,na)`;
   `list_next_var_rename (CONS x xs) ssa (na:num) =
        // Write this way to make it ascending, can also use acc passing
        (let (y,ssa',na') = next_var_rename x ssa na in
        let (ys,ssa'',na'') = list_next_var_rename xs ssa' na' in
          (CONS y ys,ssa'',na''))`];;

let fake_move_def = new_definition
  `(fake_move v:'a wordLang_prog) = wordLang_Inst (asm_Const v (n2w
  0))`;;

(*Do the merging moves only*)
let merge_moves_def,merge_moves_ind = define_rec
  [`word_alloc_merge_moves [] ssa_L ssa_R (na:num) =
  ([],[],na,ssa_L,ssa_R)`;
   `word_alloc_merge_moves (CONS x xs) ssa_L ssa_R (na:num) =
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
            (CONS Lmove seqL,CONS Rmove seqR,na' + 4,
                              sptree_insert x na'
                                ssa_L',sptree_insert x na' ssa_R'))
                                | _2 ->
                                (seqL,seqR,na',ssa_L',ssa_R'))`];;

(* tracking priority of moves
  0 = unprioritized
  1 = base "high" priority
  2 = higher priority than base

  T, INL <- left side
  F, INR <- right side
*)
let priority_def = new_definition
  `priority x1 b =
        match x1 with
          NONE -> 1
        | (SOME (INL one)) ->
       (if b then 2 else 1)
        | (SOME (INR one)) ->
       (if b then 1 else 2)`;;

(*Separately do the fake moves*)
let fake_moves_def,fake_moves_ind = define_rec
  [`fake_moves prio [] ssa_L ssa_R (na:num) = ((wordLang_Skip:'a
  wordLang_prog),(wordLang_Skip:'a wordLang_prog),na,ssa_L,ssa_R)`;
   `fake_moves prio (CONS x xs) ssa_L ssa_R (na:num) =
        (let (seqL,seqR,na',ssa_L',ssa_R') =
          fake_moves prio xs ssa_L ssa_R na in
        let optLx = sptree_lookup x ssa_L' in
        let optLy = sptree_lookup x ssa_R' in
        match (optLx,optLy) with
          (NONE,SOME Ly) ->
            (let Lmove = linear_scan_Seq seqL (fake_move na') in
            let Rmove = linear_scan_Seq seqR (wordLang_Move
              (priority prio F) [(na',Ly)]) in
            (Lmove,Rmove,na' + 4,sptree_insert x na'
              ssa_L',sptree_insert x na' ssa_R')) | (SOME Lx,NONE) ->
            (let Lmove = linear_scan_Seq seqL (wordLang_Move
              (priority prio T) [(na',Lx)]) in
            let Rmove = linear_scan_Seq seqR (fake_move na') in
            (Lmove,Rmove,na' + 4,sptree_insert x na'
              ssa_L',sptree_insert x na' ssa_R')) | _4 ->
              (seqL,seqR,na',ssa_L',ssa_R'))`];;

let fix_inconsistencies_def = new_definition
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
(* Note: this needs to return a prog to support specific registers for AddCarry and other special insts
*)
let ssa_cc_trans_inst_def = new_definition
  `ssa_cc_trans_inst x ssa na =
        match x with
          asm_Skip -> (wordLang_Skip,ssa,na)
        | (wordLang_Const reg w) ->
       (let (reg',ssa',na') = next_var_rename reg ssa na in
         (wordLang_Inst (asm_Const reg' w),ssa',na'))
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       (match ri with
         Reg r3 ->
         (let r3' = option_lookup ssa r3 in
         let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_Arith (asm_Binop bop r1' r2' (Reg
             r3'))),ssa',na')) | _5 ->
         (let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_Arith (asm_Binop bop r1' r2'
             ri)),ssa',na')))
        | (asm_Arith (asm_Shift shift' r1 r2 ri)) ->
       (match ri with Reg r3 ->
         (let r3' = option_lookup ssa r3 in
         let r2' = option_lookup ssa r2 in
         let mov_in = (wordLang_Move 1) [(8,r3')] in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (linear_scan_Seq mov_in (wordLang_Inst (asm_Arith
             (asm_Shift shift' r1' r2' (Reg 8)))),ssa',na')) | _6 ->
         (let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_Arith (asm_Shift shift' r1' r2'
             ri)),ssa',na')))
        | (asm_Arith (asm_Div r1 r2 r3)) ->
       (let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       (wordLang_Inst (asm_Arith (asm_Div r1' r2' r3')),ssa',na'))
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
       (let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       let r4' = option_lookup ssa r4 in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let mov_in = (wordLang_Move 1) [(0,r4')] in
       let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r4'',0)] in
         (linear_scan_Seq mov_in (linear_scan_Seq (wordLang_Inst
           (asm_Arith (asm_AddCarry r1' r2' r3' 0)))
           mov_out),ssa'',na''))
        // Note: for AddOverflow and SubOverflow, setting r4 to 0 is not necessary
        // However, this helps with word_to_stack which currently only spills
        // one register on writes
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) ->
       (let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       // TODO: This might need to be made a strong preference
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r4'',0)] in
         (linear_scan_Seq (wordLang_Inst (asm_Arith (asm_AddOverflow
           r1' r2' r3' 0))) mov_out,ssa'',na''))
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) ->
       (let r2' = option_lookup ssa r2 in
       let r3' = option_lookup ssa r3 in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r4'',0)] in
         (linear_scan_Seq (wordLang_Inst (asm_Arith (asm_SubOverflow
           r1' r2' r3' 0))) mov_out,ssa'',na''))
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) ->
       (let r3' = option_lookup ssa r3 in
       let r4' = option_lookup ssa r4 in
       let mov_in = (wordLang_Move 1) [(0,r3'); (4,r4')] in
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r2',0); (r1',6)] in
         (linear_scan_Seq mov_in (linear_scan_Seq (wordLang_Inst
           (asm_Arith (asm_LongMul 6 0 0 4))) mov_out),ssa'',na''))
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) ->
       (let r3' = option_lookup ssa r3 in
       let r4' = option_lookup ssa r4 in
       let r5' = option_lookup ssa r5 in
       let mov_in = (wordLang_Move 1) [(6,r3'); (0,r4')] in
       let (r2',ssa',na') = next_var_rename r2 ssa na in
       let (r1',ssa'',na'') = next_var_rename r1 ssa' na' in
       let mov_out = (wordLang_Move 1) [(r2',6); (r1',0)] in
         (linear_scan_Seq mov_in (linear_scan_Seq (wordLang_Inst
           (asm_Arith (asm_LongDiv 0 6 6 0 r5'))) mov_out),ssa'',na''))
        | (asm_Mem asm_Load r (Addr a w)) ->
       (let a' = option_lookup ssa a in
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_Mem asm_Load r' (Addr a' w)),ssa',na'))
        | (asm_Mem asm_Store r (Addr a w)) ->
       (let a' = option_lookup ssa a in
       let r' = option_lookup ssa r in
         (wordLang_Inst (asm_Mem asm_Store r' (Addr a' w)),ssa,na))
        | (asm_Mem asm_Load32 r (Addr a w)) ->
       (let a' = option_lookup ssa a in
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_Mem asm_Load32 r' (Addr a'
           w)),ssa',na'))
        | (asm_Mem asm_Store32 r (Addr a w)) ->
       (let a' = option_lookup ssa a in
       let r' = option_lookup ssa r in
         (wordLang_Inst (asm_Mem asm_Store32 r' (Addr a' w)),ssa,na))
        | (asm_Mem asm_Load8 r (Addr a w)) ->
       (let a' = option_lookup ssa a in
       let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_Mem asm_Load8 r' (Addr a' w)),ssa',na'))
        | (asm_Mem asm_Store8 r (Addr a w)) ->
       (let a' = option_lookup ssa a in
       let r' = option_lookup ssa r in
         (wordLang_Inst (asm_Mem asm_Store8 r' (Addr a' w)),ssa,na))
        | (asm_FP (FPLess r f1 f2)) ->
       (let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_FP (FPLess r' f1 f2)),ssa',na'))
        | (asm_FP (FPLessEqual r f1 f2)) ->
       (let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_FP (FPLessEqual r' f1 f2)),ssa',na'))
        | (asm_FP (FPEqual r f1 f2)) ->
       (let (r',ssa',na') = next_var_rename r ssa na in
         (wordLang_Inst (asm_FP (FPEqual r' f1 f2)),ssa',na'))
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       (if dimindex (:'a) = 64 then
         let (r1',ssa',na') = next_var_rename r1 ssa na in
           (wordLang_Inst (asm_FP (FPMovToReg r1' r2 d)),ssa',na')
             else
         let (r1',ssa',na') = next_var_rename r1 ssa na in
         let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
           (wordLang_Inst (asm_FP (FPMovToReg r1' r2'
             d)),ssa'',na''))
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       (if dimindex (:'a) = 64 then
         let r1' = option_lookup ssa r1 in
           (wordLang_Inst (asm_FP (FPMovFromReg d r1' 0)),ssa,na)
             else
         let r1' = option_lookup ssa r1 in
         let r2' = option_lookup ssa r2 in
         if r1' = r2' then
           // force distinct with an extra Move
           let (r2'',ssa',na') = next_var_rename r2 ssa na in
           let mov_in = (wordLang_Move 0) [(r2'',r2')] in
           (linear_scan_Seq mov_in (wordLang_Inst (asm_FP
             (FPMovFromReg d r1' r2''))),
           ssa',na') else
           (wordLang_Inst (asm_FP (FPMovFromReg d r1' r2')),ssa,na))
        // Catchall -- for future instructions to be added, and all other FP
        | x -> (wordLang_Inst x,ssa,na)`;;

(*Expressions only ever need to lookup a variable's current ssa map
  so it doesn't need the other parts *)
let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let ssa_cc_trans_exp_def,ssa_cc_trans_exp_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_exp_size (\x. 0) x1)`
  [`ssa_cc_trans_exp t expr =
        match expr with
          wordLang_Var num' ->
       wordLang_Var (option_lookup t num')
        | (wordLang_Load exp) -> wordLang_Load (ssa_cc_trans_exp t
          exp)
        | (wordLang_Op wop ls) ->
       wordLang_Op wop (MAP (ssa_cc_trans_exp t) ls)
        | (wordLang_Shift sh exp nexp) ->
       wordLang_Shift sh (ssa_cc_trans_exp t exp) (ssa_cc_trans_exp
         t nexp)
        | expr -> expr`];;

(*Attempt to pull out "renaming" moves
  This takes a current name map and updates the names of all the vars
  Intended for Alloc,Call cutset restoration moves
*)
let list_next_var_rename_move_def = new_definition
  `list_next_var_rename_move ssa n ls =
     (let cur_ls = MAP (option_lookup ssa) ls in
     let (new_ls,ssa',n') = list_next_var_rename ls ssa n in
     ((wordLang_Move 0) (ZIP new_ls cur_ls),ssa',n'))`;;

(* force the renaming map to send x -> y unless
  x is already remapped *)
let force_rename_def,force_rename_ind = define_rec
  [`force_rename [] ssa = ssa`;
   `force_rename (CONS (x,y) xs) ssa =
        force_rename xs (sptree_insert x y ssa)`];;

let mk_prio_def = new_definition
  `mk_prio el er =
   (if el = wordLang_Skip then SOME (INL one) else if er =
     wordLang_Skip then SOME (INR one) else NONE)`;;

(*Generate reconciliation moves from current ssa to target ssa for vars in ns.

  For v ∈ ns ∩ domain cur_ssa: emit a Move from cur_ssa(v) to tgt_ssa(v)
  (skipped if they happen to be the same register).

  For v ∈ ns with v ∉ domain cur_ssa: emit nothing. Such v are vacuous
  in strong_locals_rel (ssa_locals_rel ⇒ v ∉ domain st.locals), and when
  the enclosing Loop's cut_state reads tgt_ssa(v), it either succeeds
  because v was added to cur_ssa later (so Case 3 in the proof analysis
  applies: position tgt_ssa(v) = v gets moved), or the source cut also
  fails, making the theorem vacuous.*)
let ssa_reconcile_def = new_definition
  `ssa_reconcile cur_ssa tgt_ssa ns =
     (let vars' = MAP FST (toAList ns) in
     let moves = FILTER (\(a,b). ~(a = b))
       (FLAT (MAP (\v.
         match sptree_lookup v cur_ssa with NONE -> [] | SOME cur_v
           -> [(option_lookup tgt_ssa v,cur_v)]) vars')) in
     if moves = [] then (wordLang_Skip:'a wordLang_prog) else
       wordLang_Move 1 moves)`;;

(* Loop entry setup: refresh ssa for vars in (names ∪ exit_names) so that
   option_lookup ssa_refreshed is INJ on each. For vars already in ssa we
   emit a real Move; for vars not in ssa we allocate fresh ssa entries
   and fake_move-initialise the corresponding target registers. *)
let loop_setup_def = new_definition
  `loop_setup (names:1 spt) (exit_names:1 spt) ssa na =
     (let all_vars_ls = MAP FST (toAList (sptree_union names
       exit_names)) in
     let extend_ls = FILTER (\v. sptree_lookup v ssa = NONE)
       all_vars_ls in
     let refresh_ls = FILTER (\v. IS_SOME (sptree_lookup v ssa))
       all_vars_ls in
     let (fresh_pos_ls,ssa_ext,na_ext) =
       list_next_var_rename extend_ls ssa na in
     let fake_prog = ITLIST linear_scan_Seq
       (MAP (\r. fake_move r) fresh_pos_ls) (wordLang_Skip:'a
         wordLang_prog) in
     let (refresh_mov,ssa_refreshed,na_refreshed) =
       list_next_var_rename_move ssa_ext na_ext refresh_ls in
     (linear_scan_Seq fake_prog
       refresh_mov,ssa_refreshed,na_refreshed))`;;

let ssa_cc_trans_def,ssa_cc_trans_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`ssa_cc_trans wordLang_Skip ssa na lt = (wordLang_Skip,ssa,na)`;
   `ssa_cc_trans (wordLang_Move pri ls) ssa na lt =
        (let ls_1 = MAP FST ls in
        let ls_2 = MAP SND ls in
        let ren_ls2 = MAP (option_lookup ssa) ls_2 in
        let (ren_ls1,ssa',na') = list_next_var_rename ls_1 ssa na in
        let force =
          FILTER (\(x,y). ~(MEM x ls_1)) (ZIP ls_2 ren_ls1) in
          (wordLang_Move pri (ZIP ren_ls1 ren_ls2),force_rename
            force ssa',na'))`;
   `ssa_cc_trans (wordLang_StoreConsts a b c d ws) ssa na lt =
        (let c1 = option_lookup ssa c in
        let d1 = option_lookup ssa d in
        let (d2,ssa',na') = next_var_rename d ssa na in
        let (c2,ssa'',na'') = next_var_rename c ssa' na' in
        let prog = wordLang_Seq ((wordLang_Move 1) [(4,c1); (6,d1)])
          (wordLang_Seq (wordLang_StoreConsts 0 2 4 6 ws)
               ((wordLang_Move 1) [(c2,4); (d2,6)])) in
        (prog,ssa'',na''))`;
   `ssa_cc_trans (wordLang_Inst i) ssa na lt =
        (let (i',ssa',na') = ssa_cc_trans_inst i ssa na in
          (i',ssa',na'))`;
   `ssa_cc_trans (wordLang_Assign num' exp) ssa na lt =
        (let exp' = ssa_cc_trans_exp ssa exp in
        let (num',ssa',na') = next_var_rename num' ssa na in
          (wordLang_Assign num' exp',ssa',na'))`;
   `ssa_cc_trans (wordLang_Get num' store) ssa na lt =
        (let (num',ssa',na') = next_var_rename num' ssa na in
          (wordLang_Get num' store,ssa',na'))`;
   `ssa_cc_trans (wordLang_Store exp num') ssa na lt =
        (let exp' = ssa_cc_trans_exp ssa exp in
        let num' = option_lookup ssa num' in
          (wordLang_Store exp' num',ssa,na))`;
   `ssa_cc_trans (wordLang_Seq s1 s2) ssa na lt =
        (let (s1',ssa',na') = ssa_cc_trans s1 ssa na lt in
        let (s2',ssa'',na'') = ssa_cc_trans s2 ssa' na' lt in
          (wordLang_Seq s1' s2',ssa'',na''))`;
   `ssa_cc_trans (wordLang_MustTerminate s1) ssa na lt =
        (let (s1',ssa',na') = ssa_cc_trans s1 ssa na lt in
          (wordLang_MustTerminate s1',ssa',na'))`;
   `// Tricky pmatch 1: we need to merge the ssa results from both branches by
    // unSSA-ing the phi functions
    ssa_cc_trans (wordLang_If cmp r1 ri e2 e3) ssa na lt =
     (let r1' = option_lookup ssa r1 in
     let ri' = (match ri with Reg r -> Reg (option_lookup ssa r) |
       Imm v -> Imm v) in
     // ssa is the copy for both branches,
     // however, we can use new na2 and ns2
     let (e2',ssa2,na2) = ssa_cc_trans e2 ssa na lt in
     // ssa2 is the ssa map for the first branch
     let (e3',ssa3,na3) = ssa_cc_trans e3 ssa na2 lt in
     // ssa3 is the ssa map for the second branch, notice we
     // continued using na2 here though!
     // prioritizing original skips
     let prio = mk_prio e2' e3' in
     let (e2_cons,e3_cons,na_fin,ssa_fin) =
       fix_inconsistencies prio ssa2 ssa3 na3 in
     (wordLang_If cmp r1' ri' (wordLang_Seq e2' e2_cons)
       (wordLang_Seq e3' e3_cons),ssa_fin,na_fin))`;
   `// For cutsets, we must restart the ssa mapping to maintain consistency
    ssa_cc_trans (wordLang_Alloc num' numset) ssa na lt =
     (let all_names' = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList all_names') in
     // This trick allows us to not keep the "next stack" variable by
     // simply starting from the next available stack location
     // Assuming na is an alloc var of course..
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na +
       2) ls in
     let num' = option_lookup ssa' num' in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset
       in
     // Restart the ssa map
     let ssa_cut = inter ssa' all_names' in
     let (ret_mov,ssa'',na'') =
       list_next_var_rename_move ssa_cut (na' + 2) ls in
     let prog = (wordLang_Seq (stack_mov)
                (wordLang_Seq ((wordLang_Move 1) [(2,num')])
                (wordLang_Seq (wordLang_Alloc 2 stack_set)
                  (ret_mov)))) in
     (prog,ssa'',na''))`;
   `ssa_cc_trans (wordLang_Raise num') ssa na lt =
        (let num' = option_lookup ssa num' in
        let mov = (wordLang_Move 1) [(2,num')] in
        (wordLang_Seq mov (wordLang_Raise 2),ssa,na))`;
   `ssa_cc_trans (wordLang_OpCurrHeap b dst src) ssa na lt =
        (let src' = option_lookup ssa src in
        let (dst',ssa',na') = next_var_rename dst ssa na in
          (wordLang_OpCurrHeap b dst' src',ssa',na'))`;
   `ssa_cc_trans (wordLang_Return num' nums) ssa na lt =
        (let num' = option_lookup ssa num' in
        let nums' = MAP (option_lookup ssa) nums in
        let rets = list_of_seq (\x. 2 * (x + 1)) (LENGTH nums') in
        let mov = wordLang_Move 0 (ZIP rets nums') in
        (wordLang_Seq mov (wordLang_Return num' rets),ssa,na))`;
   `ssa_cc_trans wordLang_Tick ssa na lt = (wordLang_Tick,ssa,na)`;
   `ssa_cc_trans (wordLang_Set n exp) ssa na lt =
        (let exp' = ssa_cc_trans_exp ssa exp in
        (wordLang_Set n exp',ssa,na))`;
   `ssa_cc_trans (wordLang_LocValue r l1) ssa na lt =
        (let (r',ssa',na') = next_var_rename r ssa na in
          (wordLang_LocValue r' l1,ssa',na'))`;
   `ssa_cc_trans (wordLang_Install ptr len dptr dlen numset) ssa na lt =
        (let all_names' = sptree_union (FST numset) (SND numset) in
        let ls = MAP FST (toAList all_names') in
        let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na
          + 2) ls in
        let stack_set = apply_nummaps_key (option_lookup ssa')
          numset in
        let ptr' = option_lookup ssa' ptr in
        let len' = option_lookup ssa' len in
        let dptr' = option_lookup ssa' dptr in
        let dlen' = option_lookup ssa' dlen in
        let ssa_cut = inter ssa' all_names' in
        let (ptr'',ssa'',na'') = next_var_rename ptr ssa_cut (na' +
          2) in
        let (ret_mov,ssa''',na''') =
          list_next_var_rename_move ssa'' na'' ls in
        let prog = (wordLang_Seq (stack_mov)
                   (wordLang_Seq ((wordLang_Move 1) [(2,ptr');
                     (4,len')])
                   (wordLang_Seq (wordLang_Install 2 4 dptr' dlen'
                     stack_set)
                   (wordLang_Seq ((wordLang_Move 1) [(ptr'',2)])
                     ret_mov)))) in
        (prog,ssa''',na'''))`;
   `ssa_cc_trans (wordLang_CodeBufferWrite r1 r2) ssa na lt =
        (let r1' = option_lookup ssa r1 in
        let r2' = option_lookup ssa r2 in
        (wordLang_CodeBufferWrite r1' r2',ssa,na))`;
   `ssa_cc_trans (wordLang_DataBufferWrite r1 r2) ssa na lt =
        (let r1' = option_lookup ssa r1 in
        let r2' = option_lookup ssa r2 in
        (wordLang_DataBufferWrite r1' r2',ssa,na))`;
   `ssa_cc_trans (wordLang_FFI ffi_index ptr1 len1 ptr2 len2 numset) ssa
  na lt =
        (let all_names' = sptree_union (FST numset) (SND numset) in
        let ls = MAP FST (toAList all_names') in
        let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na
          + 2) ls in
        let stack_set = apply_nummaps_key (option_lookup ssa')
          numset in
        let cptr1 = option_lookup ssa' ptr1 in
        let clen1 = option_lookup ssa' len1 in
        let cptr2 = option_lookup ssa' ptr2 in
        let clen2 = option_lookup ssa' len2 in
        let ssa_cut = inter ssa' all_names' in
        let (ret_mov,ssa'',na'') =
          list_next_var_rename_move ssa_cut (na' + 2) ls in
        let prog = (wordLang_Seq (stack_mov)
                   (wordLang_Seq ((wordLang_Move 1) [(2,cptr1);
                     (4,clen1); (6,cptr2); (8,clen2)])
                   (wordLang_Seq (wordLang_FFI ffi_index 2 4 6 8
                     stack_set) (ret_mov)))) in
        (prog,ssa'',na''))`;
   `ssa_cc_trans (wordLang_Call NONE dest args h) ssa na lt =
        (let names = MAP (option_lookup ssa) args in
        let conv_args = list_of_seq (\x. 2 * x) (LENGTH names) in
        let move_args = ((wordLang_Move 1) (ZIP conv_args names)) in
        let prog = wordLang_Seq move_args (wordLang_Call NONE dest
          conv_args h) in
          (prog,ssa,na))`;
   `ssa_cc_trans (wordLang_Call (SOME (ret,numset,ret_handler,l1,l2))
  dest args h) ssa na lt =
        (let all_names' = sptree_union (FST numset) (SND numset) in
        let ls = MAP FST (toAList all_names') in
        let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na
          + 2) ls in
        let stack_set = apply_nummaps_key (option_lookup ssa')
          numset in
        let names = MAP (option_lookup ssa) args in
        let conv_args = list_of_seq (\x. 2 * (x + 1)) (LENGTH names)
          in
        let move_args = ((wordLang_Move 1) (ZIP conv_args names)) in
        let ssa_cut = inter ssa' all_names' in
        let (ret_mov,ssa'',na'') =
          list_next_var_rename_move ssa_cut (na' + 2) ls in
        // ret_mov restores the cutset
        // This recurses on the returning handler
        let (ret',ssa_2_p,na_2_p) = list_next_var_rename ret ssa''
          na'' in
        let (ren_ret_handler,ssa_2,na_2) =
          ssa_cc_trans ret_handler ssa_2_p na_2_p lt in
        let regs' = list_of_seq (\x. 2 * (x + 1)) (LENGTH ret) in
        let mov_ret_handler =
            (wordLang_Seq ret_mov (wordLang_Seq ((wordLang_Move 1)
              (ZIP ret' regs')) (ren_ret_handler))) in
        (match h with
          NONE ->
            (let prog =
              (wordLang_Seq stack_mov (wordLang_Seq move_args
              (wordLang_Call (SOME
                (regs',stack_set,mov_ret_handler,l1,l2))
                    dest conv_args NONE))) in
            (prog,ssa_2,na_2)) | SOME (n,h,l1',l2') ->
            (let (n',ssa_3_p,na_3_p) = next_var_rename n ssa'' na_2
              in
            let (ren_exc_handler,ssa_3,na_3) =
                (ssa_cc_trans h ssa_3_p na_3_p lt) in
            let mov_exc_handler =
                (wordLang_Seq ret_mov (wordLang_Seq ((wordLang_Move
                  1) [n',2]) (ren_exc_handler))) in
            let prio = mk_prio mov_ret_handler mov_exc_handler in
            let (ret_cons,exc_cons,na_fin,ssa_fin) =
                fix_inconsistencies prio ssa_2 ssa_3 na_3 in
            let cons_ret_handler = wordLang_Seq mov_ret_handler
              ret_cons in
            let cons_exc_handler = wordLang_Seq mov_exc_handler
              exc_cons in
            let prog =
                (wordLang_Seq stack_mov (wordLang_Seq move_args
                (wordLang_Call (SOME
                  (regs',stack_set,cons_ret_handler,l1,l2))
                   dest conv_args (SOME
                     (2,cons_exc_handler,l1',l2'))))) in
            (prog,ssa_fin,na_fin))))`;
   `ssa_cc_trans (wordLang_ShareInst op v exp) ssa na lt =
        (let exp' = ssa_cc_trans_exp ssa exp in
          if op = asm_Store \/ op = asm_Store8 \/ op = asm_Store16
            \/ op = asm_Store32 then
            (wordLang_ShareInst op (option_lookup ssa v)
              exp',ssa,na) else
            let (v',ssa',na') = next_var_rename v ssa na in
              (wordLang_ShareInst op v' exp',ssa',na'))`;
   `// Loop: use loop_setup to refresh ssa for (names ∪ exit_names) before
    // the Loop, establishing INJ on their domains by construction. Body sees
    // ssa restricted to names; lt carries ssa_refreshed (full) for
    // Break/Continue reconciliation.
    ssa_cc_trans (wordLang_Loop names body exit_names) ssa na lt =
     (let (setup_prog,ssa_refreshed,na_refreshed) =
       loop_setup names exit_names ssa na in
     let ssa_names = apply_nummap_key (option_lookup ssa_refreshed)
       names in
     let ssa_exit = apply_nummap_key (option_lookup ssa_refreshed)
       exit_names in
     let ssa_body = inter ssa_refreshed names in
     let (body',ssa',na') =
       ssa_cc_trans body ssa_body na_refreshed
         (CONS (ssa_refreshed,names,exit_names) lt) in
     let back_moves = ssa_reconcile ssa' ssa_refreshed names in
     let body_final = (if back_moves = wordLang_Skip then body' else
       wordLang_Seq body' back_moves) in
     (wordLang_Seq setup_prog (wordLang_Loop ssa_names body_final
       ssa_exit),
      inter ssa_refreshed exit_names,na'))`;
   `// Break n: reconcile current ssa with target exit ssa
    ssa_cc_trans (wordLang_Break n) ssa na lt =
     (match oEL n lt with
       NONE -> (wordLang_Break n,ssa,na) | SOME
         (tgt_ssa,names,exit_names) ->
         (let moves = ssa_reconcile ssa tgt_ssa exit_names in
         ((if moves = wordLang_Skip then wordLang_Break n else
           wordLang_Seq moves (wordLang_Break n)),ssa,na)))`;
   `// Continue n: reconcile current ssa with target entry ssa
    ssa_cc_trans (wordLang_Continue n) ssa na lt =
     (match oEL n lt with
       NONE -> (wordLang_Continue n,ssa,na) | SOME
         (tgt_ssa,names,exit_names) ->
         (let moves = ssa_reconcile ssa tgt_ssa names in
         ((if moves = wordLang_Skip then wordLang_Continue n
           else wordLang_Seq moves (wordLang_Continue n)),ssa,na)))`];;

(*Recursively applying colours to a program*)

let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let apply_colour_exp_def,apply_colour_exp_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_exp_size (\x. 0) x1)`
  [`apply_colour_exp f expr =
        match expr with
          wordLang_Var num' -> wordLang_Var (f num')
        | (wordLang_Load exp) -> wordLang_Load (apply_colour_exp f
          exp)
        | (wordLang_Op wop ls) -> wordLang_Op wop (MAP
          (apply_colour_exp f) ls)
        | (wordLang_Shift sh exp nexp) -> wordLang_Shift sh
          (apply_colour_exp f exp) (apply_colour_exp f nexp)
        | expr -> expr`];;

let apply_colour_imm_def = new_definition
  `apply_colour_imm f x =
        match x with
          Reg n -> Reg (f n)
        | x -> x`;;

let apply_colour_inst_def = new_definition
  `apply_colour_inst f x =
        match x with
          asm_Skip -> wordLang_Skip
        | (wordLang_Const reg w) -> wordLang_Const (f reg) w
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       asm_Arith (asm_Binop bop (f r1) (f r2) (apply_colour_imm f
         ri))
        | (asm_Arith (asm_Shift shift' r1 r2 ri)) ->
       asm_Arith (asm_Shift shift' (f r1) (f r2) (apply_colour_imm f
         ri))
        | (asm_Arith (asm_Div r1 r2 r3)) ->
       asm_Arith (asm_Div (f r1) (f r2) (f r3))
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
       asm_Arith (asm_AddCarry (f r1) (f r2) (f r3) (f r4))
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) ->
       asm_Arith (asm_AddOverflow (f r1) (f r2) (f r3) (f r4))
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) ->
       asm_Arith (asm_SubOverflow (f r1) (f r2) (f r3) (f r4))
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) ->
       asm_Arith (asm_LongMul (f r1) (f r2) (f r3) (f r4))
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) ->
       asm_Arith (asm_LongDiv (f r1) (f r2) (f r3) (f r4) (f r5))
        | (asm_Mem asm_Load r (Addr a w)) ->
       asm_Mem asm_Load (f r) (Addr (f a) w)
        | (asm_Mem asm_Store r (Addr a w)) ->
       asm_Mem asm_Store (f r) (Addr (f a) w)
        | (asm_Mem asm_Load32 r (Addr a w)) ->
       asm_Mem asm_Load32 (f r) (Addr (f a) w)
        | (asm_Mem asm_Store32 r (Addr a w)) ->
       asm_Mem asm_Store32 (f r) (Addr (f a) w)
        | (asm_Mem asm_Load8 r (Addr a w)) ->
       asm_Mem asm_Load8 (f r) (Addr (f a) w)
        | (asm_Mem asm_Store8 r (Addr a w)) ->
       asm_Mem asm_Store8 (f r) (Addr (f a) w)
        | (asm_FP (FPLess r f1 f2)) -> asm_FP (FPLess (f r) f1 f2)
        | (asm_FP (FPLessEqual r f1 f2)) -> asm_FP (FPLessEqual (f r)
          f1 f2)
        | (asm_FP (FPEqual r f1 f2)) -> asm_FP (FPEqual (f r) f1 f2)
        | (asm_FP (FPMovToReg r1 r2 d)) -> asm_FP (FPMovToReg (f r1)
          (f r2) d)
        | (asm_FP (FPMovFromReg d r1 r2)) -> asm_FP (FPMovFromReg d
          (f r1) (f r2))
        | x -> x`;;
(*Catchall -- for future instructions to be added*)

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let apply_colour_def,apply_colour_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`apply_colour f p =
        match p with
          wordLang_Skip -> wordLang_Skip
        | (wordLang_Move pri ls) ->
       wordLang_Move pri (ZIP (MAP (f o FST) ls) (MAP (f o SND) ls))
        | (wordLang_Inst i) -> wordLang_Inst (apply_colour_inst f i)
        | (wordLang_Assign num' exp) -> wordLang_Assign (f num')
          (apply_colour_exp f exp)
        | (wordLang_Get num' store) -> wordLang_Get (f num') store
        | (wordLang_Store exp num') -> wordLang_Store
          (apply_colour_exp f exp) (f num')
        | (wordLang_Call ret dest args h) ->
       (let ret = (match ret with NONE -> NONE | SOME
         (vs,cutset,ret_handler,l1,l2) ->
                             SOME (MAP f vs,apply_nummaps_key f
                               cutset,apply_colour f
                               ret_handler,l1,l2)) in
       let args = MAP f args in
       let h = (match h with NONE -> NONE | SOME (v,prog,l1,l2) ->
         SOME (f v,apply_colour f prog,l1,l2)) in
         wordLang_Call ret dest args h)
        | (linear_scan_Seq s1 s2) -> wordLang_Seq (apply_colour f
          s1) (apply_colour f s2)
        | (wordLang_MustTerminate s1) -> wordLang_MustTerminate
          (apply_colour f s1)
        | (wordLang_If cmp r1 ri e2 e3) ->
       wordLang_If cmp (f r1) (apply_colour_imm f ri) (apply_colour
         f e2) (apply_colour f e3)
        | (wordLang_Install r1 r2 r3 r4 numset) ->
       wordLang_Install (f r1) (f r2) (f r3) (f r4)
         (apply_nummaps_key f numset)
        | (wordLang_CodeBufferWrite r1 r2) ->
       wordLang_CodeBufferWrite (f r1) (f r2)
        | (wordLang_DataBufferWrite r1 r2) ->
       wordLang_DataBufferWrite (f r1) (f r2)
        | (wordLang_FFI ffi_index ptr1 len1 ptr2 len2 numset) ->
       wordLang_FFI ffi_index (f ptr1) (f len1) (f ptr2) (f len2)
         (apply_nummaps_key f numset)
        | (wordLang_LocValue r l1) ->
       wordLang_LocValue (f r) l1
        | (wordLang_Alloc num' numset) ->
       wordLang_Alloc (f num') (apply_nummaps_key f numset)
        | (wordLang_StoreConsts a b c d ws) ->
       wordLang_StoreConsts (f a) (f b) (f c) (f d) ws
        | (wordLang_Raise num') -> wordLang_Raise (f num')
        | (wordLang_Return num1 nums) -> wordLang_Return (f num1)
          (MAP f nums)
        | wordLang_Tick -> wordLang_Tick
        | (reg_alloc_Set n exp) -> wordLang_Set n (apply_colour_exp
          f exp)
        | (wordLang_OpCurrHeap b n1 n2) -> wordLang_OpCurrHeap b (f
          n1) (f n2)
        | (wordLang_ShareInst op v exp) -> wordLang_ShareInst op (f
          v) (apply_colour_exp f exp)
        | (wordLang_Loop names body exit_names) ->
       wordLang_Loop (apply_nummap_key f names) (apply_colour f
         body) (apply_nummap_key f exit_names)
        | p -> p`];;


(* Liveness Analysis*)

(*Writes made by any inst as a sptree*)
let get_writes_inst_def = new_definition
  `get_writes_inst inst' =
        match inst' with
          asm_Const reg w -> sptree_insert reg one LN
        | (asm_Arith (asm_Binop bop r1 r2 ri)) -> sptree_insert r1
          one LN
        | (asm_Arith (asm_Shift shift' r1 r2 ri)) -> sptree_insert r1
          one LN
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
        | (asm_Mem asm_Load r (Addr a w)) -> sptree_insert r one LN
        | (asm_Mem asm_Load32 r (Addr a w)) -> sptree_insert r one LN
        | (asm_Mem asm_Load8 r (Addr a w)) -> sptree_insert r one LN
        | (asm_FP (FPLess r f1 f2)) -> sptree_insert r one LN
        | (asm_FP (FPLessEqual r f1 f2)) -> sptree_insert r one LN
        | (asm_FP (FPEqual r f1 f2)) -> sptree_insert r one LN
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
       (if dimindex (:'a) = 64 then sptree_insert r1 one LN else
         sptree_insert r2 one (sptree_insert r1 one LN))
        | inst' -> LN`;;

(*Liveness for instructions, follows liveness equations
  live-sets are num_sets a.k.a. unit-sptrees*)
let get_live_inst_def = new_definition
  `get_live_inst x live =
        match x with
          asm_Skip -> live
        | (wordLang_Const reg w) -> sptree_delete reg live
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       (match ri with Reg r3 -> sptree_insert r2 one (sptree_insert
         r3 one (sptree_delete r1 live)) | _7 -> sptree_insert r2 one
         (sptree_delete r1 live))
        | (asm_Arith (asm_Shift shift' r1 r2 ri)) ->
       (match ri with Reg r3 -> sptree_insert r2 one (sptree_insert
         r3 one (sptree_delete r1 live)) | _8 -> sptree_insert r2 one
         (sptree_delete r1 live))
        | (asm_Arith (asm_Div r1 r2 r3)) ->
       (sptree_insert r3 one (sptree_insert r2 one (sptree_delete r1
         live)))
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
       // r4 is live anyway
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
        | (asm_Mem asm_Load r (Addr a w)) ->
       sptree_insert a one (sptree_delete r live)
        | (asm_Mem asm_Store r (Addr a w)) ->
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
       (if dimindex (:'a) = 64 then sptree_delete r1 live else
         sptree_delete r1 (sptree_delete r2 live))
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       (if dimindex (:'a) = 64 then sptree_insert r1 one live else
         sptree_insert r2 one (sptree_insert r1 one live))
        // Catchall -- for future instructions to be added
        | x -> live`;;

let big_union_def = new_definition
  `big_union ls = ITLIST (\x y. sptree_union x y) ls LN`;;

let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_live_exp_def,get_live_exp_ind = define_wf
  `MEASURE (\x0. wordLang_exp_size (\x. 0) x0)`
  [`get_live_exp expr =
        match expr with
          wordLang_Var num' -> sptree_insert num' one LN
        | (wordLang_Load exp) -> get_live_exp exp
        | (wordLang_Op wop ls) ->
       big_union (MAP get_live_exp ls)
        | (wordLang_Shift sh exp nexp) -> sptree_union (get_live_exp
          exp) (get_live_exp nexp)
        | expr -> LN`];;

let word_alloc_numset_list_insert_def,
    word_alloc_numset_list_insert_ind =
  define_rec
  [`word_alloc_numset_list_insert [] t = t`;
   `word_alloc_numset_list_insert (CONS x xs) t = sptree_insert x
  one (word_alloc_numset_list_insert xs t)`];;

let get_live_def,get_live_ind = define_shaped_rec
  "match"
  [`get_live x1 live lt =
        match x1 with
          wordLang_Skip -> live
        // All SNDs are read and all FSTs are written
        | (wordLang_Move pri ls) ->
       (let killed = ITLIST sptree_delete (MAP FST ls) live in
         word_alloc_numset_list_insert (MAP SND ls) killed)
        | (wordLang_Inst i) -> get_live_inst i live
        // num is written, exp is read
        | (wordLang_Assign num' exp) ->
       (let sub' = get_live_exp exp in
         sptree_union sub' (sptree_delete num' live))
        | (wordLang_Get num' store) -> sptree_delete num' live
        // Everything is read
        | (wordLang_Store exp num') ->
       sptree_insert num' one (sptree_union (get_live_exp exp) live)
        // Find liveset just before s2 which is the input liveset to s1
        | (linear_scan_Seq s1 s2) ->
       get_live s1 (get_live s2 live lt) lt
        | (wordLang_MustTerminate s1) ->
       get_live s1 live lt
        // First pmatch where branching appears:
        // We get the livesets for e2 and e3, union them, add the if variable
        // then pass the resulting liveset upwards
        | (wordLang_If cmp r1 ri e2 e3) ->
       (let e2_live = get_live e2 live lt in
       let e3_live = get_live e3 live lt in
       let union_live = sptree_union e2_live e3_live in
          match ri with Reg r2 -> sptree_insert r2 one
            (sptree_insert r1 one union_live) | _9 -> sptree_insert r1
            one union_live)
        | (wordLang_Alloc num' numset) -> sptree_insert num' one
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
        (sptree_insert ptr2 one (sptree_insert len2 one
          (sptree_union (FST numset) (SND numset)))))
        | (wordLang_StoreConsts a b c d ws) ->
        (sptree_insert c one (sptree_insert d one live))
        | (wordLang_Raise num') -> sptree_insert num' one live
        | (wordLang_Return num1 nums) -> sptree_insert num1 one
          (word_alloc_numset_list_insert nums live)
        | wordLang_Tick -> live
        | (wordLang_LocValue r l1) -> sptree_delete r live
        | (reg_alloc_Set n exp) -> sptree_union (get_live_exp exp)
          live
        | (wordLang_OpCurrHeap b n1 n2) -> sptree_insert n2 one
          (sptree_delete n1 live)
        | (wordLang_ShareInst mop v exp) ->
       (let sub' = get_live_exp exp in
         if mop = wordLang_Store \/ mop = asm_Store8 \/ mop =
           asm_Store16 \/ mop = asm_Store32 then sptree_union sub'
           (sptree_insert v one live) else sptree_union sub'
           (sptree_delete v live))
        // Loop: entry-live is names (for cut_state). Body's entry-live must be
        // covered by cut state (domain names), handled via strong_locals_rel
        // extension at proof time.
        // Break/Continue handle exit_names/names via lt.
        | (wordLang_Loop names body exit_names) -> names
        // Break n: exit_names from enclosing Loop at nesting level n
        | (wordLang_Break n) ->
       (match oEL n lt with
         NONE -> LN | SOME (names,exit_names) -> exit_names)
        // Continue n: names from enclosing Loop at nesting level n
        | (wordLang_Continue n) ->
       (match oEL n lt with
         NONE -> LN | SOME (names,exit_names) -> names)
        // Cut-set must be live, args input must be live
        // For tail calls, there shouldn't be a liveset since control flow will
        // never return into the same instance
        // Otherwise, both args + cutsets live
        | (wordLang_Call NONE dest args h) ->
          word_alloc_numset_list_insert args LN
        | (wordLang_Call (SOME (_10,cutset,_11)) dest args h) ->
       sptree_union (sptree_union (FST cutset) (SND cutset))
         (word_alloc_numset_list_insert args LN)`];;

(* Dead instruction removal *)
let remove_dead_inst_def = new_definition
  `remove_dead_inst x live =
        match (x,live) with
          (asm_Skip,(live:1 spt)) -> T
        | ((wordLang_Const reg w),live) -> (sptree_lookup reg live =
          NONE)
        | ((asm_Arith (asm_Binop bop r1 r2 ri)),live) ->
          (sptree_lookup r1 live = NONE)
        | ((asm_Arith (asm_Shift shift' r1 r2 n)),live) ->
          (sptree_lookup r1 live = NONE)
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
        | ((asm_Mem asm_Load r (Addr a w)),live) -> (sptree_lookup r
          live = NONE)
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
       (if dimindex (:'a) = 64 then sptree_lookup r1 live = NONE else
         (sptree_lookup r1 live = NONE /\ (sptree_lookup r2 live =
         NONE)))
        // Catchall -- for other instructions
        | (x,live) -> F`;;

(* Delete dead code, w.r.t. a set of live variables.
  The liveset is a tuple (live,nlive):
  - live is an sptree of live variables
  - nlive is a list of globals which are NOT live

  This code is written assuming flat_exp_conventions,
    so many trivial cases are omitted.
*)
let remove_dead_def,remove_dead_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`remove_dead prog live nlive lt =
        match prog with
          wordLang_Move pri ls ->
       (let ls = FILTER (\(x,y). sptree_lookup x live = SOME one) ls
         in
       if ls = [] then (wordLang_Skip,live,nlive) else
       let killed = ITLIST sptree_delete (MAP FST ls) live in
         (wordLang_Move pri ls,word_alloc_numset_list_insert (MAP
           SND ls) killed,nlive))
        | (wordLang_Inst i) ->
       (if remove_dead_inst i live then (wordLang_Skip,live,nlive)
         else (wordLang_Inst i,get_live_inst i live,nlive))
        | (wordLang_Get num' store) ->
       (if sptree_lookup num' live = NONE then
         (wordLang_Skip,live,nlive) else (wordLang_Get num'
           store,sptree_delete num' live,FILTER (\s. ~(store = s))
           nlive))
        | (wordLang_OpCurrHeap b num' src) ->
       (if sptree_lookup num' live = NONE then
         (wordLang_Skip,live,nlive) else (
         wordLang_OpCurrHeap b num' src,
           sptree_insert src one (sptree_delete num' live),FILTER
             (\s. ~(CurrHeap = s)) nlive))
        | (wordLang_LocValue r l1) ->
       (if sptree_lookup r live = NONE then
         (wordLang_Skip,live,nlive) else (wordLang_LocValue r
           l1,sptree_delete r live,nlive))
        | (reg_alloc_Set store_name exp) ->
       (match exp with
         wordLang_Var r ->
         (if MEM store_name nlive then
           (wordLang_Skip,live,nlive) else
           (reg_alloc_Set store_name (wordLang_Var r),sptree_insert
             r one live,CONS store_name nlive)) | _12 ->
         (let prog = reg_alloc_Set store_name exp in
           (prog,get_live prog live lt,[])))
        | (linear_scan_Seq s1 s2) ->
       (let (s2,s2live,s2nlive) = remove_dead s2 live nlive lt in
       let (s1,s1live,s1nlive) = remove_dead s1 s2live s2nlive lt in
       let prog =
         (if s1 = wordLang_Skip then
           s2 else
           if s2 = wordLang_Skip then s1 else linear_scan_Seq s1 s2)
             in (prog,s1live,s1nlive))
        | (wordLang_MustTerminate s1) ->
       // This can technically be optimized away if it was a Skip,
       // but we should never use MustTerminate to wrap completely dead code
       (let (s1,s1live,s1nlive) = remove_dead s1 live nlive lt in
         (wordLang_MustTerminate s1,s1live,s1nlive))
        | (wordLang_If cmp r1 ri e2 e3) ->
       (let (e2,e2_live,e2_nlive) = remove_dead e2 live nlive lt in
       let (e3,e3_live,e3_nlive) = remove_dead e3 live nlive lt in
       let union_live = sptree_union e2_live e3_live in
       let liveset =
          (match ri with Reg r2 -> sptree_insert r2 one
            (sptree_insert r1 one union_live) | _13 -> sptree_insert r1
            one union_live) in
       let nliveset = FILTER (\s. MEM s e3_nlive) e2_nlive in
       let prog =
         (if e2 = wordLang_Skip /\ e3 = wordLang_Skip then
           wordLang_Skip else wordLang_If cmp r1 ri e2 e3) in
       (prog,liveset,nliveset))
        | (wordLang_Call (SOME (v,cutsets,ret_handler,l1,l2)) dest
          args h) ->
       // top level
       (let args_set = word_alloc_numset_list_insert args LN in
       let cutset = sptree_union (FST cutsets) (SND cutsets) in
       let live_set = sptree_union cutset args_set in
       let (ret_handler,_14) = remove_dead ret_handler live nlive lt
         in
       let h =
         (match h with
           NONE -> NONE | SOME (v',prog,l1,l2) ->
           SOME (v',FST (remove_dead prog live nlive lt),l1,l2)) in
       (wordLang_Call (SOME (v,cutsets,ret_handler,l1,l2)) dest args
         h,(live_set,[])))
        // we should not remove the ShareInst Load instructions.
        // * It produces a ffi event even if the variable is not in
        // * the live set
        // In the cases below, we either return nlive unchanged
        // or we return [] because of control flow
        | (wordLang_Call NONE a b c) ->
       (let prog = wordLang_Call NONE a b c in
         (prog,get_live prog live lt,[]))
        | (wordLang_Alloc a b) ->
       (let prog = wordLang_Alloc a b in
         (prog,get_live prog live lt,[]))
        | (wordLang_Raise a) ->
       (let prog = wordLang_Raise a in
         (prog,get_live prog live lt,[]))
        | (wordLang_Return a b) ->
       (let prog = wordLang_Return a b in
         (prog,get_live prog live lt,[]))
        // Conservative: nlive reset to [] at Loop boundary so all stores are
        // treated as live across loop iterations (otherwise backward nlive
        // analysis could eliminate Sets whose overwrites live on a later
        // iteration).  Cost: no store-DCE across Loops; ordinary locals-DCE
        // inside the body still applies.
        | (wordLang_Loop names body exit_names) ->
       (let lt' = CONS (names,exit_names) lt in
       let (body',_15,_16) = remove_dead body names [] lt' in
       (wordLang_Loop names body' exit_names,names,[]))
        // Break/Continue reset nlive to [] because they jump past whatever
        // follows, so store-DCE cannot propagate dead-set info across them.
        | (wordLang_Break n) ->
       (let prog = wordLang_Break n in
         (prog,get_live prog live lt,[]))
        | (wordLang_Continue n) ->
       (let prog = wordLang_Continue n in
         (prog,get_live prog live lt,[]))
        | prog -> (prog,get_live prog live lt,nlive)`];;

let remove_dead_prog_def = new_definition
  `remove_dead_prog prog = FST (remove_dead prog LN [] [])`;;

(*Single step immediate writes by a prog*)
let get_writes_def = new_definition
  `get_writes prog =
        match prog with
          wordLang_Move pri ls -> word_alloc_numset_list_insert (MAP
            FST ls) LN
        | (wordLang_Inst i) -> get_writes_inst i
        | (wordLang_Assign num' exp) -> sptree_insert num' one LN
        | (wordLang_Get num' store) -> sptree_insert num' one LN
        | (wordLang_LocValue r l1) -> sptree_insert r one LN
        | (wordLang_Install r1 _17 _18 _19 _20) -> sptree_insert r1
          one LN
        | (wordLang_OpCurrHeap b r1 _21) -> sptree_insert r1 one LN
        | (wordLang_StoreConsts a b c d _22) -> sptree_insert a one
          (sptree_insert b one (sptree_insert c one (sptree_insert d one
          LN)))
        | (wordLang_ShareInst asm_Load v _23) -> sptree_insert v one
          LN
        | (wordLang_ShareInst asm_Load8 v _24) -> sptree_insert v one
          LN
        | (wordLang_ShareInst asm_Load16 v _25) -> sptree_insert v
          one LN
        | (wordLang_ShareInst asm_Load32 v _26) -> sptree_insert v
          one LN
        | prog -> LN`;;

let get_writes_pmatch = prove
 (`!inst'.
   get_writes inst' =
     (match inst' with wordLang_Move pri ls ->
       word_alloc_numset_list_insert (MAP FST ls) LN | wordLang_Inst i
       -> get_writes_inst i | wordLang_Assign num' exp ->
       sptree_insert num' one LN | wordLang_Get num' store ->
       sptree_insert num' one LN | wordLang_LocValue r l1 ->
       sptree_insert r one LN | wordLang_Install r1 _27 _28 _29 _30 ->
       sptree_insert r1 one LN | wordLang_OpCurrHeap b r1 _31 ->
       sptree_insert r1 one LN | wordLang_StoreConsts a b c d _32 ->
       sptree_insert a one (sptree_insert b one (sptree_insert c one
       (sptree_insert d one LN))) | wordLang_ShareInst asm_Load v _33
       -> sptree_insert v one LN | wordLang_ShareInst asm_Load8 v _34
       -> sptree_insert v one LN | wordLang_ShareInst asm_Load16 v _35
       -> sptree_insert v one LN | wordLang_ShareInst asm_Load32 v _36
       -> sptree_insert v one LN | prog -> LN)`,
  CHEAT_TAC);;

(* Old representation *)
(* HOL4 word_allocScript.sml:1049-1083: code that the source has in a
   comment *)

(* Potentially more efficient liveset representation for checking / allocation*)
let get_delta_inst_def = new_definition
  `get_delta_inst x =
        match x with
          asm_Skip -> reg_alloc_Delta [] []
        | (wordLang_Const reg w) -> reg_alloc_Delta [reg] []
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       (match ri with Reg r3 -> reg_alloc_Delta [r1] [r2; r3] | _37
         -> reg_alloc_Delta [r1] [r2])
        | (asm_Arith (asm_Shift shift' r1 r2 ri)) ->
       (match ri with Reg r3 -> reg_alloc_Delta [r1] [r2; r3] | _38
         -> reg_alloc_Delta [r1] [r2])
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
        | (asm_Mem asm_Load r (Addr a w)) -> reg_alloc_Delta [r] [a]
        | (asm_Mem asm_Store r (Addr a w)) -> reg_alloc_Delta [] [r;
          a]
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
       (if dimindex (:'a) = 64 then reg_alloc_Delta [r1] [] else
         reg_alloc_Delta [r1; r2] [])
        | (asm_FP (FPMovFromReg d r1 r2)) ->
       (if dimindex (:'a) = 64 then reg_alloc_Delta [] [r1] else
         reg_alloc_Delta [] [r1; r2])
        // Catchall -- for future instructions to be added
        | x -> reg_alloc_Delta [] []`;;

let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_reads_exp_def,get_reads_exp_ind = define_wf
  `MEASURE (\x0. wordLang_exp_size (\x. 0) x0)`
  [`get_reads_exp expr =
        match expr with
          wordLang_Var num' -> [num']
        | (wordLang_Load exp) -> get_reads_exp exp
        | (wordLang_Op wop ls) ->
         FLAT (MAP get_reads_exp ls)
        | (wordLang_Shift sh exp nexp) -> APPEND (get_reads_exp exp)
          (get_reads_exp nexp)
        | expr -> []`];;

let get_clash_tree_def,get_clash_tree_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`get_clash_tree wordLang_Skip lt = reg_alloc_Delta [] []`;
   `get_clash_tree (wordLang_Move pri ls) lt =
        reg_alloc_Delta (MAP FST ls) (MAP SND ls)`;
   `get_clash_tree (wordLang_Inst i) lt = get_delta_inst i`;
   `get_clash_tree (wordLang_Assign num' exp) lt = reg_alloc_Delta
  [num'] (get_reads_exp exp)`;
   `get_clash_tree (wordLang_Get num' store) lt = reg_alloc_Delta
  [num'] []`;
   `get_clash_tree (wordLang_Store exp num') lt = reg_alloc_Delta []
  (CONS num' (get_reads_exp exp))`;
   `get_clash_tree (wordLang_Seq s1 s2) lt = reg_alloc_Seq
  (get_clash_tree s1 lt) (get_clash_tree s2 lt)`;
   `get_clash_tree (wordLang_If cmp r1 ri e2 e3) lt =
        (let e2t = get_clash_tree e2 lt in
        let e3t = get_clash_tree e3 lt in
        match ri with
          Reg r2 -> reg_alloc_Seq (reg_alloc_Delta [] [r1; r2])
            (reg_alloc_Branch NONE e2t e3t) | _41 -> reg_alloc_Seq
            (reg_alloc_Delta [] [r1]) (reg_alloc_Branch NONE e2t
            e3t))`;
   `get_clash_tree (wordLang_MustTerminate s) lt =
        get_clash_tree s lt`;
   `get_clash_tree (wordLang_Alloc num' numset) lt =
        reg_alloc_Seq (reg_alloc_Delta [] [num']) (reg_alloc_Set
          (sptree_union (FST numset) (SND numset)))`;
   `get_clash_tree (wordLang_Install r1 r2 r3 r4 numset) lt =
        reg_alloc_Seq (reg_alloc_Delta [] [r4; r3; r2; r1])
          (reg_alloc_Seq (reg_alloc_Set (sptree_union (FST numset)
          (SND numset))) (reg_alloc_Delta [r1] []))`;
   `get_clash_tree (wordLang_CodeBufferWrite r1 r2) lt =
        reg_alloc_Delta [] [r2; r1]`;
   `get_clash_tree (wordLang_DataBufferWrite r1 r2) lt =
        reg_alloc_Delta [] [r2; r1]`;
   `get_clash_tree (wordLang_FFI ffi_index ptr1 len1 ptr2 len2 numset)
  lt =
        reg_alloc_Seq (reg_alloc_Delta [] [ptr1; len1; ptr2;
          len2]) (reg_alloc_Set (sptree_union (FST numset) (SND
          numset)))`;
   `get_clash_tree (wordLang_Raise num') lt = reg_alloc_Delta []
  [num']`;
   `get_clash_tree (wordLang_Return num1 nums) lt = reg_alloc_Delta
  [] (CONS num1 nums)`;
   `get_clash_tree wordLang_Tick lt = reg_alloc_Delta [] []`;
   `get_clash_tree (wordLang_LocValue r l1) lt = reg_alloc_Delta [r]
  []`;
   `get_clash_tree (wordLang_Set n exp) lt = reg_alloc_Delta []
  (get_reads_exp exp)`;
   `get_clash_tree (wordLang_OpCurrHeap b dst src) lt =
  reg_alloc_Delta [dst] [src]`;
   `get_clash_tree (wordLang_StoreConsts a b c d ws) lt =
  reg_alloc_Delta [a; b; c; d] [c; d]`;
   `get_clash_tree (wordLang_ShareInst op v exp) lt = (if op =
  wordLang_Store \/ op = asm_Store8 \/ op = asm_Store16 \/ op =
  asm_Store32 then reg_alloc_Delta [] (CONS v (get_reads_exp exp))
  else reg_alloc_Delta [v] (get_reads_exp exp))`;
   `get_clash_tree (wordLang_Loop names body exit_names) lt =
        reg_alloc_Seq (reg_alloc_Set names)
          (reg_alloc_Seq (reg_alloc_Set exit_names)
            (reg_alloc_Seq (get_clash_tree body (CONS
              (names,exit_names) lt))
              (reg_alloc_Set names)))`;
   `// Break n: exit_names vars must all be live
    get_clash_tree (wordLang_Break n) lt =
     (match oEL n lt with
       NONE -> reg_alloc_Set LN | SOME (names,exit_names) ->
         reg_alloc_Set exit_names)`;
   `// Continue n: names vars must all be live
    get_clash_tree (wordLang_Continue n) lt =
     (match oEL n lt with
       NONE -> reg_alloc_Set LN | SOME (names,exit_names) ->
         reg_alloc_Set names)`;
   `get_clash_tree (wordLang_Call ret dest args h) lt =
        (let args_set = word_alloc_numset_list_insert args LN in
        match ret with
          NONE -> reg_alloc_Set args_set | SOME
            (vs,cutsets,ret_handler,_58,_59) ->
          (let cutset = sptree_union (FST cutsets) (SND cutsets) in
          let live_set = sptree_union cutset args_set in
          // Might be inefficient..
          let ret_tree = reg_alloc_Seq (reg_alloc_Set
            (word_alloc_numset_list_insert vs cutset)) (get_clash_tree
            ret_handler lt) in
          match h with
            NONE -> reg_alloc_Seq (reg_alloc_Set live_set) ret_tree
              | SOME (v',prog,_60,_61) ->
            (let handler_tree =
              reg_alloc_Seq (reg_alloc_Set (sptree_insert v' one
                cutset)) (get_clash_tree prog lt) in
            reg_alloc_Branch (SOME live_set) ret_tree
              handler_tree)))`];;

(* Preference edges
  The allocator tries hard to coalesce these edges
*)
let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_prefs_def,get_prefs_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x0)`
  [`get_prefs prog acc =
        match prog with
          wordLang_Move pri ls -> APPEND (MAP (\(x,y). (pri,x,y))
            ls) acc
        | (wordLang_MustTerminate s1) ->
       get_prefs s1 acc
        | (linear_scan_Seq s1 s2) ->
       get_prefs s1 (get_prefs s2 acc)
        | (wordLang_If cmp num' rimm e2 e3) ->
       get_prefs e2 (get_prefs e3 acc)
        | (wordLang_Call (SOME (v,cutset,ret_handler,l1,l2)) dest
          args h) ->
       (match h with
         NONE -> get_prefs ret_handler acc | SOME (v,prog,l1,l2) ->
           get_prefs prog (get_prefs ret_handler acc))
        | (wordLang_Loop names body exit_names) -> get_prefs body
          acc
        | prog -> acc`];;

let get_prefs_pmatch = prove
 (`!s acc.
   get_prefs s acc =
     (match s with (wordLang_Move pri ls) -> APPEND (MAP (\(x,y).
       (pri,x,y)) ls) acc | (wordLang_MustTerminate s1) ->
     get_prefs s1 acc | (linear_scan_Seq s1 s2) ->
     get_prefs s1 (get_prefs s2 acc) | (wordLang_If cmp num' rimm e2
       e3) ->
     get_prefs e2 (get_prefs e3 acc) | (wordLang_Call (SOME
       (v,cutset,ret_handler,l1,l2)) dest args NONE) ->
     get_prefs ret_handler acc | (wordLang_Call (SOME
       (v,cutset,ret_handler,l1,l2)) dest args (SOME
       (_62,prog,_63,_64))) ->
     get_prefs prog (get_prefs ret_handler acc) | (wordLang_Loop
       names body exit_names) ->
     get_prefs body acc | prog -> acc)`,
  CHEAT_TAC);;

(*
  For each var, we collect 5 tuples indicating the number of
  instructions in which it is involved in:
    (lhs const,lhs reg,lhs memory, rhs reg, rhs memory)

  Currently, this just treats FP as a "reg" instruction

  This is meant to be small and quick to compute, because it has to be applied
  to the entire program just before register allocation, which can be huge.

*)

new_type_abbrev("heu_data",`: num#num#num#num#num`);;

let _ = do_list hide_constant ["mem"];;

let add1_lhs_const_def = new_definition
  `add1_lhs_const x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (1,0,0,0,0) t | SOME (const,reg,mem',rreg,rmem)
       ->
     sptree_insert x (const + 1,reg,mem',rreg,rmem) t)`;;

let add1_lhs_reg_def = new_definition
  `add1_lhs_reg x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,1,0,0,0) t | SOME (const,reg,mem',rreg,rmem)
       ->
     sptree_insert x (const,reg + 1,mem',rreg,rmem) t)`;;

let add1_lhs_mem_def = new_definition
  `add1_lhs_mem x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,0,1,0,0) t | SOME (const,reg,mem',rreg,rmem)
       ->
     sptree_insert x (const,reg,mem' + 1,rreg,rmem) t)`;;

let add1_rhs_reg_def = new_definition
  `add1_rhs_reg x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,0,0,1,0) t | SOME (const,reg,mem',rreg,rmem)
       ->
     sptree_insert x (const,reg,mem',rreg + 1,rmem) t)`;;

let add1_rhs_mem_def = new_definition
  `add1_rhs_mem x (t:(num#num#num#num#num) spt) =
   (match sptree_lookup x t with NONE ->
     sptree_insert x (0,0,0,0,1) t | SOME (const,reg,mem',rreg,rmem)
       ->
     sptree_insert x (const,reg,mem',rreg,rmem + 1) t)`;;

let get_heu_inst_def = new_definition
  `get_heu_inst x tup =
        match x with
          asm_Skip -> tup
        | (wordLang_Const reg w) ->
       (add1_lhs_const reg tup)
        | (asm_Arith (asm_Binop bop r1 r2 ri)) ->
       (match ri with
         Reg r3 ->
           (
            // r1 := r2 op r3
            add1_lhs_reg r1
           (add1_rhs_reg r3 (add1_rhs_reg r2 tup))) | _65 ->
           (add1_lhs_reg r1
           (add1_rhs_reg r2 tup)))
        | (asm_Arith (asm_Shift shift' r1 r2 ri)) ->
       (match ri with
         Reg r3 ->
           (
            // r1 := r2 (shift) r3
            add1_lhs_reg r1
           (add1_rhs_reg r3 (add1_rhs_reg r2 tup))) | _66 ->
           (add1_lhs_reg r1
           (add1_rhs_reg r2 tup)))
        | (asm_Arith (asm_Div r1 r2 r3)) ->
        (add1_lhs_reg r1
        (add1_rhs_reg r3 (add1_rhs_reg r2 tup)))
        | (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
        (
         // r1,r4 := r2,r3,r4
         add1_lhs_reg r4 (add1_lhs_reg r1
        (add1_rhs_reg r4 (add1_rhs_reg r3 (add1_rhs_reg r2 tup)))))
        | (asm_Arith (asm_AddOverflow r1 r2 r3 r4)) ->
        (
         // r1,r4 := r2,r3
         add1_lhs_reg r4 (add1_lhs_reg r1
        (add1_rhs_reg r3 (add1_rhs_reg r2 tup))))
        | (asm_Arith (asm_SubOverflow r1 r2 r3 r4)) ->
        (
         // r1,r4 := r2,r3
         add1_lhs_reg r4 (add1_lhs_reg r1
        (add1_rhs_reg r3 (add1_rhs_reg r2 tup))))
        | (asm_Arith (asm_LongMul r1 r2 r3 r4)) ->
        (
         // r1,r2 := r3,r4
         add1_lhs_reg r2 (add1_lhs_reg r1
        (add1_rhs_reg r4 (add1_rhs_reg r3 tup))))
        | (asm_Arith (asm_LongDiv r1 r2 r3 r4 r5)) ->
        (
         // r1,r2 := r3,r4,r5
         add1_lhs_reg r2 (add1_lhs_reg r1
        (add1_rhs_reg r5 (add1_rhs_reg r4 (add1_rhs_reg r3 tup)))))
        | (asm_Mem asm_Load r (Addr a w)) ->
        (add1_lhs_mem r tup)
        | (asm_Mem asm_Store r (Addr a w)) ->
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
        // Catchall -- for future instructions to be added, and all other FP
        | x -> tup`;;

(* For Ifs, as a heuristic we take the max over branching paths *)
let heu_max_def = new_definition
  `heu_max (c1,r1,m1,rr1,rm1) (c2,r2,m2,rr2,rm2) =
     (MAX c1 c2,MAX r1 r2,MAX m1 m2,MAX rr1 rr2,MAX rm1 rm2)`;;

let heu_max_all_def = new_definition
  `heu_max_all t1 t2 =
   (let t1r = difference t1 t2 in
   // everything in t1 not already in t2
   sptree_union
   t1r
   (mllist_mapi (\k v.
     match sptree_lookup k t1 with
       NONE -> v | SOME v' -> heu_max v v') t2))`;;

let heu_merge_call_def = new_definition
  `heu_merge_call (t1:1 spt) t2 =
   sptree_union t1 t2`;;

(* We use "lr" to approximate any new vars not already tracked in calls *)
let add_call_def = new_definition
  `(add_call lr calls':1 spt) =
   sptree_union (sptree_map (\v. one) lr) calls'`;;

let get_heu_def,get_heu_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`get_heu fc f lr =
        match (f,lr) with
          (wordLang_Move pri ls,(lr,calls')) ->
       (ITLIST add1_lhs_reg
       (MAP FST ls)
       (ITLIST add1_rhs_reg (MAP SND ls) lr),calls')
        | ((wordLang_Inst i),(lr,calls')) -> (get_heu_inst i
          lr,calls')
        | ((wordLang_Get num' store),(lr,calls')) ->
       (add1_lhs_mem num' lr,calls')
        | ((reg_alloc_Set _67 exp),(lr,calls')) ->
       (match exp with (wordLang_Var r) ->
          (add1_rhs_mem r lr,calls') | _68 -> (lr,calls'))
        // General Set exp ignored
        | ((wordLang_OpCurrHeap b dst src),(lr,calls')) ->
       (add1_lhs_reg dst (add1_rhs_reg src lr),calls')
        | ((wordLang_LocValue r l1),(lr,calls')) ->
       (add1_lhs_reg r lr,calls')
        | ((linear_scan_Seq s1 s2),lr) -> get_heu fc s2 (get_heu fc
          s1 lr)
        | ((wordLang_MustTerminate s1),lr) -> get_heu fc s1 lr
        | ((wordLang_If cmp r1 ri e2 e3),lr) ->
       (let (lr2,calls2) = get_heu fc e2 lr in
       let (lr3,calls3) = get_heu fc e3 lr in
       let lr = heu_max_all lr2 lr3 in
       let calls' = heu_merge_call (calls2:1 spt) calls3 in
       ((match ri with
         Reg r2 -> add1_rhs_reg r1 (add1_rhs_reg r2 lr) | _69 ->
         add1_rhs_reg r1 lr),calls'))
        | ((wordLang_Call NONE dest args h),(lr,calls')) ->
       (match dest with
         NONE -> (lr,calls') | SOME p ->
         (if p = fc then (lr,add_call lr calls') else (lr,calls')))
        | ((wordLang_Call (SOME (_70,_71,e2,_72,_73)) dest args
          h),(lr,calls')) ->
       (let calls' =
         (match dest with NONE -> calls' | SOME p ->
           (if p = fc then (add_call lr calls') else calls')) in
       let (lr2,calls2) = (get_heu fc e2 (lr,calls')) in
       match h with
         NONE -> (lr2,calls') | SOME (_74,e3,_75,_76) ->
         (let (lr3,calls3) = get_heu fc e3 (lr,calls') in
         (heu_max_all lr2 lr3,heu_merge_call calls2 calls3)))
        | ((wordLang_ShareInst asm_Load r _77),(lr,calls')) ->
          (add1_lhs_mem r lr,calls')
        | ((wordLang_ShareInst asm_Load8 r _78),(lr,calls')) ->
          (add1_lhs_mem r lr,calls')
        | ((wordLang_ShareInst asm_Load16 r _79),(lr,calls')) ->
          (add1_lhs_mem r lr,calls')
        | ((wordLang_ShareInst asm_Load32 r _80),(lr,calls')) ->
          (add1_lhs_mem r lr,calls')
        | ((wordLang_ShareInst asm_Store r _81),(lr,calls')) ->
          (add1_rhs_mem r lr,calls')
        | ((wordLang_ShareInst asm_Store8 r _82),(lr,calls')) ->
          (add1_rhs_mem r lr,calls')
        | ((wordLang_ShareInst asm_Store16 r _83),(lr,calls')) ->
          (add1_rhs_mem r lr,calls')
        | ((wordLang_ShareInst asm_Store32 r _84),(lr,calls')) ->
          (add1_rhs_mem r lr,calls')
        | ((wordLang_Loop names body exit_names),lr) -> get_heu fc
          body lr
        // The remaining ones are exps, or otherwise unimportant from the
        // pov of register allocation, since all their temps are already forced into
        // specific registers
        // Omitted: Skip, Assign, Store, FFI, Alloc, Raise, Tick, Call NONE
        | (f,lrc) -> lrc`];;

(* Forced edges for certain instructions *)
let _ = size_thms "asm_config";;
let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_forced_def,get_forced_ind = define_wf
  `MEASURE (\(x0,x1,x2). asm_config_size (\x. 0) x0 +
  wordLang_prog_size (\x. 0) x1)`
  [`get_forced c prog acc =
        match (c,prog) with
          ((c:'a asm_config),((wordLang_Inst i):'a wordLang_prog))
            ->
       (match i with
         asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
          (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
            then APPEND (APPEND (if r1 = r3 then [] else [(r1,r3)])
             (if r1 = r4 then [] else [(r1,r4)]))
             acc else acc) | asm_Arith (asm_AddOverflow r1 r2 r3 r4)
               ->
          (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
            then APPEND (if r1 = r3 then [] else [(r1,r3)])
             acc else acc) | asm_Arith (asm_SubOverflow r1 r2 r3 r4)
               ->
          (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
            then APPEND (if r1 = r3 then [] else [(r1,r3)])
             acc else acc) | asm_Arith (asm_LongMul r1 r2 r3 r4) ->
          (if (asm_config_ISA c = ARMv7) then APPEND (if (r1 = r2)
            then [] else [(r1,r2)]) acc else if (asm_config_ISA c =
            ARMv8) \/ (asm_config_ISA c = RISC_V) \/ (asm_config_ISA c
            = Ag32) then APPEND (APPEND (if r1 = r3 then [] else
            [(r1,r3)])
            (if r1 = r4 then [] else [(r1,r4)]))
            acc else
            acc) | asm_FP (FPMovToReg r1 r2 d) -> APPEND (if
              dimindex (:'a) = 32 /\ ~(r1 = r2) then [(r1,r2)] else [])
              acc | asm_FP (FPMovFromReg d r1 r2) -> APPEND (if
              dimindex (:'a) = 32 /\ ~(r1 = r2) then [(r1,r2)] else [])
              acc | _85 -> acc)
        | (c,(wordLang_MustTerminate s1)) ->
       get_forced c s1 acc
        | (c,(linear_scan_Seq s1 s2)) ->
       get_forced c s1 (get_forced c s2 acc)
        | (c,(wordLang_If cmp num' rimm e2 e3)) ->
       get_forced c e2 (get_forced c e3 acc)
        | (c,(wordLang_Call (SOME (v,cutset,ret_handler,l1,l2)) dest
          args h)) ->
       (match h with
         NONE -> get_forced c ret_handler acc | SOME (v,prog,l1,l2)
           -> get_forced c prog (get_forced c ret_handler acc))
        | (c,(wordLang_Loop names body exit_names)) -> get_forced c
          body acc
        | (c,prog) -> acc`];;

let get_forced_pmatch = prove
 (`!c prog acc.
   (get_forced (c:'a asm_config) prog acc =
     (match prog with
       wordLang_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
        (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
          then APPEND (APPEND (if r1 = r3 then [] else [(r1,r3)])
           (if r1 = r4 then [] else [(r1,r4)]))
           acc else acc) | wordLang_Inst (asm_Arith (asm_AddOverflow
             r1 r2 r3 r4)) ->
        (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
          then APPEND (if r1 = r3 then [] else [(r1,r3)])
           acc else acc) | wordLang_Inst (asm_Arith (asm_SubOverflow
             r1 r2 r3 r4)) ->
        (if (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V)
          then APPEND (if r1 = r3 then [] else [(r1,r3)])
           acc else acc) | wordLang_Inst (asm_Arith (asm_LongMul r1
             r2 r3 r4)) ->
        (if (asm_config_ISA c = ARMv7) then APPEND (if (r1 = r2) then
          [] else [(r1,r2)]) acc else if (asm_config_ISA c = ARMv8) \/
          (asm_config_ISA c = RISC_V) \/ (asm_config_ISA c = Ag32) then
          APPEND (APPEND (if r1 = r3 then [] else [(r1,r3)])
          (if r1 = r4 then [] else [(r1,r4)]))
          acc else
          acc) | wordLang_Inst (asm_FP (FPMovToReg r1 r2 d)) ->
            APPEND (if dimindex (:'a) = 32 /\ ~(r1 = r2) then [(r1,r2)]
            else []) acc | wordLang_Inst (asm_FP (FPMovFromReg d r1 r2))
            -> APPEND (if dimindex (:'a) = 32 /\ ~(r1 = r2) then
            [(r1,r2)] else []) acc | wordLang_MustTerminate s1 ->
            get_forced c s1 acc | linear_scan_Seq s1 s2 -> get_forced c
            s1 (get_forced c s2 acc) | wordLang_If cmp num' rimm e2 e3
            ->
       get_forced c e2 (get_forced c e3 acc) | wordLang_Call (SOME
         (v,cutset,ret_handler,l1,l2)) dest args NONE ->
       get_forced c ret_handler acc | wordLang_Call (SOME
         (v,cutset,ret_handler,l1,l2)) dest args (SOME
         (_86,prog,_87,_88)) ->
       get_forced c prog (get_forced c ret_handler acc) |
         wordLang_Loop names body exit_names ->
       get_forced c body acc | _89 -> acc))`,
  CHEAT_TAC);;

(*col is injective over every cut set*)
let check_colouring_ok_alt_def,check_colouring_ok_alt_ind = define_rec
  [`check_colouring_ok_alt col [] = T`;
   `check_colouring_ok_alt col (CONS x xs) <=>
        (let names = MAP (col o FST) (toAList x) in
          ALL_DISTINCT names /\ check_colouring_ok_alt col xs)`];;

let every_even_colour_def = new_definition
  `every_even_colour col <=>
   ALL (\(x,y). if is_phy_var x then y = x DIV 2 else T) (toAList
     col)`;;

(*Extract a colouring function from the generated sptree*)
let total_colour_def = new_definition
  `total_colour col x =
     (match sptree_lookup x col with NONE -> (if is_phy_var x then
       x else 0) | SOME x -> 2 * x)`;;

let total_colour_alt = prove
 (`total_colour col = (\x. 2 * x) o (sp_default col)`,
  CHEAT_TAC);;

(*Check that the oracle provided colour (if it exists) is okay*)
let oracle_colour_ok_def = new_definition
  `oracle_colour_ok k col_opt tree prog ls =
   (match col_opt with
     NONE -> NONE | SOME col ->
      (let tcol = total_colour col in
      if (every_even_colour col /\ ~(check_clash_tree tcol tree LN LN
        = NONE)) then
        let prog = apply_colour tcol prog in
        if
          // Note: possibly avoid these checks and instead check the oracle domain directly
          // every_var is_phy_var prog ∧
          every_stack_var (\x. x >= 2 * k) prog /\
          ALL (\(x,y). ~((tcol x) = (tcol y))) ls then
          SOME prog else
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
let canonize_moves_aux_def,canonize_moves_aux_ind = define_rec
  [`canonize_moves_aux curp curm ctr [] acc = CONS (ctr,curp,curm)
  acc`;
   `canonize_moves_aux curp curm ctr (CONS (p,m) xs) acc =
        (if curm = m then
          canonize_moves_aux (MAX curp p) m (ctr + 1) xs acc else
          canonize_moves_aux p m 1 xs (CONS (ctr,curp,curm)
            acc))`];;

let canonize_moves_def = new_definition
  `canonize_moves ls =
   (let can1 = MAP (\((p:num),((x:num),(y:num))). if (x <= y) then
     (p,(x,y)) else (p,(y,x))) ls in
   let can2 = sort
     (\(p1,(x1,y1)) (p2,(x2,y2)).
       if x1 = x2 then
         if y1 = y2 then
           p1 < p2 else y1 < y2 else x1 < x2) can1 in
   match can2 with [] -> [] | (CONS (p,m) xs) ->
     canonize_moves_aux p m 1 xs [])`;;

(* TODO: ALL of these magic numbers must be adjusted!! *)

let get_spillcost_def = new_definition
  `get_spillcost (c,lr,lm,rr,rm) istail =
   (c + 2 * lr + 4 * lm + 2 * rr + 4 * rm) *
   (if istail then 5 else 1)`;;

(*
  Prioritize moves that happen a lot, and have high max priority
  also give some weight to the spill cost of their endpoints
*)
let get_coalescecost_def = new_definition
  `get_coalescecost spillcost (n,p,x,y) =
   (let xcost = (if sptree_lookup x spillcost = NONE then 0 else 1)
     in
   let ycost = (if sptree_lookup y spillcost = NONE then 0 else 1) in
   (n * (10 * (p + 1) + xcost + ycost),(x,y)))`;;

let get_heuristics_def = new_definition
  `get_heuristics alg fc prog =
   (if alg MOD 2 = 1 then
     let (lr,calls') = get_heu fc prog (LN,LN) in
     let moves = get_prefs prog [] in
     let spillcosts = mllist_mapi (\k v. get_spillcost v
       (sptree_lookup k calls' = NONE)) lr in
     let canon_moves = canonize_moves moves in
     let heu_moves = MAP (get_coalescecost spillcosts) canon_moves in
     (heu_moves,SOME spillcosts) else
     let moves = get_prefs prog [] in
     (moves,NONE))`;;

let select_reg_alloc_def = new_definition
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
let merge_stack_only_def = new_definition
  `merge_stack_only (x,y) (ts,fs) =
   (if sptree_lookup x ts = SOME one then
     let ts = (if is_alloc_var y then sptree_insert y one ts else ts)
       in
     let fs = (if is_phy_var y then fs else sptree_insert x one fs)
       in
     (ts,fs) else
     if is_stack_var x then
       let ts = (if is_alloc_var y then sptree_insert y one ts else
         ts) in
       (ts,fs) else
       (sptree_delete y ts,fs))`;;

let merge_stack_sets_def = new_definition
  `merge_stack_sets (ts,fs) (tsL,fsL) (tsR,fsR) =
   (let keep1 = inter tsR (inter tsL ts) in
   let keep2 = sptree_union (difference tsL ts) (difference tsR ts)
     in
     (sptree_union keep1 keep2,sptree_union fsL fsR))`;;

let remove_temp_stack_def = new_definition
  `remove_temp_stack ls (ts,fs) =
     (ITLIST sptree_delete ls ts,fs)`;;

(* Alloc variables that are already stack or
  only ever involved in stack moves *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let get_stack_only_aux_def,get_stack_only_aux_ind = define_guess_cheat
  [`get_stack_only_aux tfs prog =
        match prog with
          wordLang_Move pri ls ->
       ITLIST merge_stack_only ls tfs
        | (linear_scan_Seq s1 s2) ->
       get_stack_only_aux (get_stack_only_aux tfs s2) s1
        | (wordLang_If cmp r1 ri e2 e3) ->
       (let tfsL = get_stack_only_aux tfs e2 in
       let tfsR = get_stack_only_aux tfs e3 in
       let tfsM = merge_stack_sets tfs tfsL tfsR in
         match ri with
           Reg r2 -> remove_temp_stack [r1; r2] tfsM | _90 ->
             remove_temp_stack [r1] tfsM)
        | (wordLang_MustTerminate s) ->
       get_stack_only_aux tfs s
        | (wordLang_Call ret dest args h) ->
       (match ret with
         NONE -> tfs | SOME (v,cutset,ret_handler,_91,_92) ->
         (let rettfs = get_stack_only_aux tfs ret_handler in
         match h with
           NONE -> rettfs | SOME (v',handler,_93,_94) ->
           (let handlertfs =
             get_stack_only_aux tfs handler in
           merge_stack_sets tfs rettfs handlertfs)))
        | (wordLang_Loop names body exit_names) ->
       get_stack_only_aux tfs body
        | prog ->
       (match get_clash_tree prog [] with
         reg_alloc_Delta ws rs -> remove_temp_stack (APPEND ws
           rs) tfs | _95 -> tfs)`];;

let get_stack_only_def = new_definition
  `get_stack_only prog = SND (get_stack_only_aux (LN,LN) prog)`;;

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
let word_alloc_def = new_definition
  `word_alloc fc c alg k prog col_opt =
   (let tree = get_clash_tree prog [] in
   let fs = get_stack_only prog in
   // let moves = get_prefs_sp prog [] in
   let forced = get_forced c prog [] in
   match oracle_colour_ok k col_opt tree prog forced with
     NONE ->
       (let (heu_moves,spillcosts) = get_heuristics alg fc prog in
       (match select_reg_alloc alg spillcosts k heu_moves tree forced
         fs with
         M_success col ->
           apply_colour (total_colour col) prog | M_failure _96 ->
             prog)) |
     // cannot happen
     SOME col_prog ->
       col_prog)`;;

(*The initial move, ssa and limit vars*)
let setup_ssa_def = new_definition
  `setup_ssa n lim (prog:'a wordLang_prog) =
   (let args = even_list n in
   let (new_ls,ssa',n') = list_next_var_rename args LN lim in
     ((wordLang_Move 1) (ZIP new_ls args),ssa',n'))`;;

let limit_var_def = new_definition
  `limit_var prog =
     (let x = max_var prog in
     x + (4 - (x MOD 4)) + 1)`;;

let full_ssa_cc_trans_def = new_definition
  `full_ssa_cc_trans n prog =
     (let lim = limit_var prog in
     let (mov,ssa,na) = setup_ssa n lim prog in
     let (prog',ssa',na') = ssa_cc_trans prog ssa na [] in
       linear_scan_Seq mov prog')`;;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["inst";
   "mem"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
