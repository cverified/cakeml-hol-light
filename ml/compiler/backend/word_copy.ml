(* ======================================================== *)
(*  word_copy: ported from HOL4's
    compiler/backend/word_copyScript.sml
    A definition theory, with 14 definitions, 1 datatype and no
    theorems.  Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  This compilation pass performs a copy propagation phase.
  NOTE: Copy propagation may be incomplete if input is not in SSA form.
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_copy"
  ["reg_alloc"; "wordLang"];;

(*
  The copy propagator does the "propagation" but
    does not delete the old copy, i.e.:

  {a}
  b := a
  {b}
  c := b
  {c}
  (any future use of a or b would be replaced by c)

  The propagator state consists of
  1) a map from vars to its equivalence class
  2) a map from equivalence class to its representative
  3) a counter to generate fresh equivalences
  4) a partial map from store_names to a vars holding its value

  Only alloc vars (is_alloc_var) are ever stored in
    this mapping because we never want to
    copy propagate the others.
*)

let copy_state_FIELDS = define_record "copy_state"
  [(* maps var to its equivalence class *)
   "to_eq","num spt";
   (* maps equivalence class to its representative *)
   "from_eq","num spt";
   (* maps store names to an equivalence class *)
   "store_to_eq","(store_name#num) list";
   "next","num"];;

let empty_eq_def = new_definition
  `empty_eq =
     mk_copy_state LN LN [] 0`;;

(* lookup representative of eq class, if it exists
  otherwise it's just the var itself *)
let lookup_eq_def = new_definition
  `lookup_eq cs v =
   match sptree_lookup v (copy_state_to_eq cs) with
     NONE -> v
   | SOME c ->
     (match sptree_lookup c (copy_state_from_eq cs) with
       NONE -> v
     | SOME v' -> v')`;;

let lookup_eq_imm_def = new_definition
  `lookup_eq_imm cs vi =
   match vi with
     Reg v -> Reg (lookup_eq cs v)
   | _ -> vi`;;

(* remove v from its equivalence class,
    possibly destroying the entire class
  In SSA, this should never happen, so
  we simply drop the entire eq state if it does *)
let remove_eq_def = new_definition
  `remove_eq cs v =
   match sptree_lookup v (copy_state_to_eq cs) with
     NONE -> cs
   | SOME c -> empty_eq`;;
(*
    let to_eq = delete v cs.to_eq in
    (case lookup v cs.from_eq of
      NONE => cs with to_eq := to_eq
    | SOME v' =>
      if v = v' then
        cs with from_eq := LN
      else
        cs with to_eq := to_eq) *)

let remove_eqs_def,remove_eqs_ind = define_rec
  `(remove_eqs cs [] = cs) /\
   (remove_eqs cs (CONS v vs) =
        remove_eqs (remove_eq cs v) vs)`;;

let copy_prop_inst_def = new_definition
  `copy_prop_inst x1 cs =
     match x1 with
       asm_Skip -> (word_Skip,cs)
     | asm_Const reg w ->
       (word_Inst (asm_Const reg w),remove_eq cs reg)
     | asm_Arith (asm_Binop bop r1 r2 ri) ->
       let cs' = remove_eq cs r1 in
       let r2' = lookup_eq cs r2 in
       let ri' = lookup_eq_imm cs ri in
       let ri'' = (if ri' = Reg r1 then ri else ri') in
       (word_Inst (asm_Arith (asm_Binop bop r1 r2' ri'')),cs')
     | asm_Arith (asm_Shift backend_common_word_shift r1 r2 n) ->
       let cs' = remove_eq cs r1 in
       let r2' = lookup_eq cs r2 in
       let n' = lookup_eq_imm cs n in
       let n'' = (if n' = Reg r1 then n else n') in
       (word_Inst (asm_Arith (asm_Shift backend_common_word_shift r1 r2'
         n'')),cs')
     | asm_Arith (asm_Div r1 r2 r3) ->
       let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       (word_Inst (asm_Arith (asm_Div r1 r2' r3')),
           remove_eq cs r1)
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
       // r4 is both read from and written to
       let cs' = remove_eqs cs [r1; r4] in
       let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       let r3'' = (if r3' = r1 then r3 else r3') in
       (word_Inst (asm_Arith (asm_AddCarry r1 r2' r3'' r4)),cs')
     | asm_Arith (asm_AddOverflow r1 r2 r3 r4) ->
       let cs' = remove_eqs cs [r1; r4] in
       let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       let r3'' = (if r3' = r1 then r3 else r3') in
       (word_Inst (asm_Arith (asm_AddOverflow r1 r2' r3'' r4)),cs')
     | asm_Arith (asm_SubOverflow r1 r2 r3 r4) ->
       let cs' = remove_eqs cs [r1; r4] in
       let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       let r3'' = (if r3' = r1 then r3 else r3') in
       (word_Inst (asm_Arith (asm_SubOverflow r1 r2' r3'' r4)),cs')
     | asm_Arith (asm_LongMul r1 r2 r3 r4) ->
       let r3' = lookup_eq cs r3 in
       let r4' = lookup_eq cs r4 in
       (word_Inst (asm_Arith (asm_LongMul r1 r2 r3 r4)),
           remove_eqs cs [r1; r2])
     | asm_Arith (asm_LongDiv r1 r2 r3 r4 r5) ->
       let r3' = lookup_eq cs r3 in
       let r4' = lookup_eq cs r4 in
       let r5' = lookup_eq cs r5 in
       (word_Inst (asm_Arith (asm_LongDiv r1 r2 r3' r4' r5')),
           remove_eqs cs [r2; r1])
     | asm_Mem asm_Load r (Addr a w) ->
       let a' = lookup_eq cs a in
         (word_Inst (asm_Mem asm_Load r (Addr a' w)),
           remove_eq cs r)
     | asm_Mem asm_Store r (Addr a w) ->
       let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (word_Inst (asm_Mem asm_Store r' (Addr a' w)),cs)
     | asm_Mem asm_Load8 r (Addr a w) ->
       let a' = lookup_eq cs a in
         (word_Inst (asm_Mem asm_Load8 r (Addr a' w)),
           remove_eq cs r)
     | asm_Mem asm_Store8 r (Addr a w) ->
       let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (word_Inst (asm_Mem asm_Store8 r' (Addr a' w)),cs)
     | asm_Mem asm_Load16 r (Addr a w) ->
       let a' = lookup_eq cs a in
         (word_Inst (asm_Mem asm_Load16 r (Addr a' w)),
           remove_eq cs r)
     | asm_Mem asm_Store16 r (Addr a w) ->
       let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (word_Inst (asm_Mem asm_Store16 r' (Addr a' w)),cs)
     | asm_Mem asm_Load32 r (Addr a w) ->
       let a' = lookup_eq cs a in
         (word_Inst (asm_Mem asm_Load32 r (Addr a' w)),
           remove_eq cs r)
     | asm_Mem asm_Store32 r (Addr a w) ->
       let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (word_Inst (asm_Mem asm_Store32 r' (Addr a' w)),cs)
     | asm_FP (FPLess r f1 f2) ->
         (word_Inst (asm_FP (FPLess r f1 f2)),
           remove_eq cs r)
     | asm_FP (FPLessEqual r f1 f2) ->
         (word_Inst (asm_FP (FPLessEqual r f1 f2)),
           remove_eq cs r)
     | asm_FP (FPEqual r f1 f2) ->
         (word_Inst (asm_FP (FPEqual r f1 f2)),
           remove_eq cs r)
     | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
         (word_Inst (asm_FP (FPMovToReg r1 r2 d)),
           remove_eqs cs [r1; r2])
     | asm_FP (FPMovFromReg d r1 r2) ->
         let r1' = lookup_eq cs r1 in
         let r2' = lookup_eq cs r2 in
         let (r1'',r2'') = (if r1' = r2' then (r1,r2) else (r1',r2')) in
         (word_Inst (asm_FP (FPMovFromReg d r1'' r2'')),cs)
     // Catchall: all FP
     | asm_FP x -> (word_Inst (asm_FP x),cs)
     // Catchall: should not happen
     | _ -> ARB`;;

(* handle x := y by making x the new
  class representative of y.
  x must be guaranteed to not have to_eq *)
let set_eq_def = new_definition
  `set_eq cs x y =
   if is_alloc_var x /\ is_alloc_var y then
     match
       (match sptree_lookup y (copy_state_to_eq cs) with
         NONE -> NONE
       | SOME c -> if sptree_lookup c (copy_state_from_eq cs) = NONE then
         NONE else SOME c) with
        NONE ->
       mk_copy_state (sptree_insert x (copy_state_next cs) (sptree_insert y
         (copy_state_next cs) (copy_state_to_eq cs))) (sptree_insert
         (copy_state_next cs) x (copy_state_from_eq cs))
         (copy_state_store_to_eq cs) (copy_state_next cs + 1)
     | SOME c ->
       mk_copy_state (sptree_insert x c (copy_state_to_eq cs))
         (sptree_insert c x (copy_state_from_eq cs)) (copy_state_store_to_eq
         cs) (copy_state_next cs)
   else cs`;;

(* Handle Store <- y
  If y has no equivalence class,
    create a singleton equivalence class for y
  Otherwise, reuse the existing class for y.
  Note: SSA ensures y is always an alloc_var, so the else branch is dead code.
*)
let set_store_eq_def = new_definition
  `set_store_eq cs s y =
   if is_alloc_var y then
     match
       (match sptree_lookup y (copy_state_to_eq cs) with
         NONE -> NONE
       | SOME c -> if sptree_lookup c (copy_state_from_eq cs) = NONE then
         NONE else SOME c) with
       NONE ->
       mk_copy_state (sptree_insert y (copy_state_next cs) (copy_state_to_eq
         cs)) (sptree_insert (copy_state_next cs) y (copy_state_from_eq cs))
         (CONS (s,copy_state_next cs) (copy_state_store_to_eq cs))
         (copy_state_next cs + 1)
     | SOME c -> copy_state_store_to_eq_fupd (K (CONS (s,c)
       (copy_state_store_to_eq cs)))
       cs
   else empty_eq`;;

let lookup_store_eq_def = new_definition
  `lookup_store_eq cs s =
   match ALOOKUP (copy_state_store_to_eq cs) s with
     NONE -> NONE
   | SOME c ->
     (match sptree_lookup c (copy_state_from_eq cs) with
       NONE -> NONE
     | SOME v' -> SOME v')`;;

(* conservatively merge two equivalence classes *)
let merge_eqs_def = new_definition
  `merge_eqs cs ds =
   mk_copy_state (inter_eq (copy_state_to_eq cs) (copy_state_to_eq ds))
     (inter_eq (copy_state_from_eq cs) (copy_state_from_eq ds))
         (FILTER (\(s,c). ALOOKUP (copy_state_store_to_eq cs) s = SOME c /\
                         ALOOKUP (copy_state_store_to_eq ds) s = SOME c)
                           (copy_state_store_to_eq cs)) (MAX
                           (copy_state_next cs) (copy_state_next ds))`;;

(* shouldn't matter whether we put y or y' in set_eq? *)
let copy_prop_move_def,copy_prop_move_ind = define_rec
  `(copy_prop_move [] cs = ([],cs)) /\
   (copy_prop_move (CONS (x,y) xs) cs =
        let y' = lookup_eq cs y in
        let (ms,cs') = copy_prop_move xs cs in
        let cs'' = set_eq (remove_eq cs' x) x y in
        (CONS (x,y') ms,cs''))`;;

let copy_prop_share_def = new_definition
  `copy_prop_share exp cs =
     match exp with
     word_Var r -> word_Var (lookup_eq cs r)
   | (word_Op asm_Add [word_Var r; word_Const c]) ->
      word_Op asm_Add [word_Var (lookup_eq cs r); word_Const c]
   | _ -> exp`;;

let copy_prop_prog_def,copy_prop_prog_ind = define_shaped_rec
  "match"
  `copy_prop_prog prog cs =
     match prog with
       (word_Skip:'a word_prog) ->
       (word_Skip,cs)
     | word_Move pri xs ->
       let tt = MAP FST xs in let ss = MAP SND xs in
       if ALL (\t. ~(MEM t ss)) tt then
         // set (MAP FST xs) ∩ set (MAP SND xs) = ∅
         let (xs',cs') = copy_prop_move xs cs in
         (word_Move pri xs',cs')
       else (word_Move pri xs,empty_eq)
     | word_Inst i ->
       copy_prop_inst i cs
     | word_Return v1 v2 ->
       let v1' = lookup_eq cs v1 in
       let v2' = MAP (lookup_eq cs) v2 in
         (word_Return v1' v2',cs)
     | word_Raise v ->
       let v' = lookup_eq cs v in
         (word_Raise v',cs)
     | word_OpCurrHeap b dst src ->
       let src' = lookup_eq cs src in
       let src'' = (if src' = dst then src else src') in
         (word_OpCurrHeap b dst src'',
            remove_eq cs dst)
     | word_Tick -> (word_Tick,cs)
     | word_MustTerminate p1 ->
       let (p1',cs') = copy_prop_prog p1 cs in
       (word_MustTerminate p1',cs')
     | word_Seq p1 p2 ->
        let (q1,cs') = copy_prop_prog p1 cs in
        let (q2,cs'') = copy_prop_prog p2 cs' in
          (word_Seq q1 q2,cs'')
     | word_If cmp r ri p1 p2 ->
        let r' = lookup_eq cs r in
        let ri' = lookup_eq_imm cs ri in
        // TODO: same mapping going in
        let (q1,cs') = copy_prop_prog p1 cs in
        let (q2,cs'') = copy_prop_prog p2 cs in
          (word_If cmp r' ri' q1 q2,
          merge_eqs cs' cs'')
     | word_Set name exp ->
       (match exp with
         word_Var n ->
         let n' = lookup_eq cs n in
         (word_Set name (word_Var n'),set_store_eq cs name n)
       | _ -> (word_Set name exp,empty_eq))
     // flat_exp
     | word_Get n name ->
       (match lookup_store_eq cs name with
         NONE ->
           (word_Get n name,set_store_eq (remove_eq cs n) name n)
       | SOME v ->
         if ~(v = n) then
         let (xs',cs') = copy_prop_move [(n,v)] cs in
           (word_Move 0 xs',cs')
         else (word_Skip,cs))
     | word_Call ret dest args handler ->
       (word_Call ret dest args handler,empty_eq)
     // args will be 0,2,4,...
     // TODO: are handlers worth analyzing?
     | word_Alloc r live ->
        (word_Alloc r live,empty_eq)
     | word_StoreConsts a b c d ws ->
         (word_StoreConsts a b c d ws,
           remove_eqs cs [a; b; c; d])
     | word_LocValue r l1 ->
         (word_LocValue r l1,remove_eq cs r)
     | word_Install r1 r2 r3 r4 live ->
        (word_Install r1 r2 r3 r4 live,empty_eq)
     | word_CodeBufferWrite r1 r2 ->
        let r1' = lookup_eq cs r1 in
        let r2' = lookup_eq cs r2 in
        (word_CodeBufferWrite r1' r2',cs)
     | word_DataBufferWrite r1 r2 ->
        let r1' = lookup_eq cs r1 in
        let r2' = lookup_eq cs r2 in
        (word_DataBufferWrite r1' r2',cs)
     | word_FFI i r1 r2 r3 r4 live ->
       (word_FFI i r1 r2 r3 r4 live,empty_eq)
     | word_ShareInst op v exp ->
       let exp' = copy_prop_share exp cs in
       (word_ShareInst op v exp',
         remove_eq cs v)
     // Conservative: optimizes body from empty state. Could be smarter by
     // tracking copy facts across iterations via Break/Continue flow.
     | word_Loop names c exit_names ->
        let (c',_) = copy_prop_prog c empty_eq in
          (word_Loop names c' exit_names,empty_eq)
     | word_Break k -> (word_Break k,cs)
     | word_Continue k -> (word_Continue k,cs)
     | prog -> (prog,empty_eq)
     // impossible?`;;

let copy_prop_def = new_definition
  `copy_prop (e:'a word_prog) =
     FST (copy_prop_prog e empty_eq)`;;

(* and the interface *)
let _ = unhide_overloads ();;
