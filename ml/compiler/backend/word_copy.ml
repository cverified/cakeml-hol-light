(* ======================================================== *)
(*  word_copy: ported from HOL4's
    compiler/backend/word_copyScript.sml  *)
(* ======================================================== *)

(*
  This compilation pass performs a copy propagation phase.
  NOTE: Copy propagation may be incomplete if input is not in SSA form.
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

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
  ["to_eq","num spt";
   "from_eq","num spt";
   "store_to_eq","(store_name#num) list";
   "next","num"];;
hol4_overload "next" "copy_state_next";;
hol4_overload "next_fupd" "copy_state_next_fupd";;

let empty_eq_def = cake_define
  `empty_eq =
     mk_copy_state LN LN [] 0`;;

(* lookup representative of eq class, if it exists
  otherwise it's just the var itself *)
let lookup_eq_def = cake_define
  `lookup_eq cs v =
   (match sptree_lookup v (copy_state_to_eq cs) with
     NONE -> v | SOME c ->
     (match sptree_lookup c (copy_state_from_eq cs) with
       NONE -> v | SOME v' -> v'))`;;

let lookup_eq_imm_def = cake_define
  `lookup_eq_imm cs vi =
   (match vi with
     Reg v -> Reg (lookup_eq cs v) | _1 -> vi)`;;

(* remove v from its equivalence class,
    possibly destroying the entire class
  In SSA, this should never happen, so
  we simply drop the entire eq state if it does *)
let remove_eq_def = cake_define
  `remove_eq cs v =
   (match sptree_lookup v (copy_state_to_eq cs) with
     NONE -> cs | SOME c -> empty_eq)`;;
(*
    let to_eq = delete v cs.to_eq in
    (case lookup v cs.from_eq of
      NONE => cs with to_eq := to_eq
    | SOME v' =>
      if v = v' then
        cs with from_eq := LN
      else
        cs with to_eq := to_eq) *)

let remove_eqs_def = cake_define_list
  [`remove_eqs cs [] = cs`;
   `remove_eqs cs (v :: vs) =
        remove_eqs (remove_eq cs v) vs`];;

let copy_prop_inst_def = cake_define
  `copy_prop_inst x1 cs =
        match x1 with
          asm_Skip -> (Skip,cs)
        | (Const reg w) ->
       (Inst (Const reg w),remove_eq cs reg)
        | (Arith (asm_Binop bop r1 r2 ri)) ->
       (let cs' = remove_eq cs r1 in
       let r2' = lookup_eq cs r2 in
       let ri' = lookup_eq_imm cs ri in
       let ri'' = if ri' = Reg r1 then ri else ri' in
       (Inst (Arith (asm_Binop bop r1 r2' ri'')),cs'))
        | (Arith (Shift shift' r1 r2 n)) ->
       (let cs' = remove_eq cs r1 in
       let r2' = lookup_eq cs r2 in
       let n' = lookup_eq_imm cs n in
       let n'' = if n' = Reg r1 then n else n' in
       (Inst (Arith (Shift shift' r1 r2' n'')),cs'))
        | (Arith (Div r1 r2 r3)) ->
       (let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       (Inst (Arith (Div r1 r2' r3')),
           remove_eq cs r1))
        | (Arith (asm_AddCarry r1 r2 r3 r4)) ->
       (let cs' = remove_eqs cs [r1; r4] in
       let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       let r3'' = if r3' = r1 then r3 else r3' in
       (Inst (Arith (asm_AddCarry r1 r2' r3'' r4)),cs'))
        | (Arith (asm_AddOverflow r1 r2 r3 r4)) ->
       (let cs' = remove_eqs cs [r1; r4] in
       let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       let r3'' = if r3' = r1 then r3 else r3' in
       (Inst (Arith (asm_AddOverflow r1 r2' r3'' r4)),cs'))
        | (Arith (asm_SubOverflow r1 r2 r3 r4)) ->
       (let cs' = remove_eqs cs [r1; r4] in
       let r2' = lookup_eq cs r2 in
       let r3' = lookup_eq cs r3 in
       let r3'' = if r3' = r1 then r3 else r3' in
       (Inst (Arith (asm_SubOverflow r1 r2' r3'' r4)),cs'))
        | (Arith (asm_LongMul r1 r2 r3 r4)) ->
       (let r3' = lookup_eq cs r3 in
       let r4' = lookup_eq cs r4 in
       (Inst (Arith (asm_LongMul r1 r2 r3 r4)),
           remove_eqs cs [r1; r2]))
        | (Arith (asm_LongDiv r1 r2 r3 r4 r5)) ->
       (let r3' = lookup_eq cs r3 in
       let r4' = lookup_eq cs r4 in
       let r5' = lookup_eq cs r5 in
       (Inst (Arith (asm_LongDiv r1 r2 r3' r4' r5')),
           remove_eqs cs [r2; r1]))
        | (asm_Mem Load r (Addr a w)) ->
       (let a' = lookup_eq cs a in
         (Inst (asm_Mem Load r (Addr a' w)),
           remove_eq cs r))
        | (asm_Mem Store r (Addr a w)) ->
       (let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (Inst (asm_Mem Store r' (Addr a' w)),cs))
        | (asm_Mem asm_Load8 r (Addr a w)) ->
       (let a' = lookup_eq cs a in
         (Inst (asm_Mem asm_Load8 r (Addr a' w)),
           remove_eq cs r))
        | (asm_Mem asm_Store8 r (Addr a w)) ->
       (let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (Inst (asm_Mem asm_Store8 r' (Addr a' w)),cs))
        | (asm_Mem asm_Load16 r (Addr a w)) ->
       (let a' = lookup_eq cs a in
         (Inst (asm_Mem asm_Load16 r (Addr a' w)),
           remove_eq cs r))
        | (asm_Mem asm_Store16 r (Addr a w)) ->
       (let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (Inst (asm_Mem asm_Store16 r' (Addr a' w)),cs))
        | (asm_Mem asm_Load32 r (Addr a w)) ->
       (let a' = lookup_eq cs a in
         (Inst (asm_Mem asm_Load32 r (Addr a' w)),
           remove_eq cs r))
        | (asm_Mem asm_Store32 r (Addr a w)) ->
       (let a' = lookup_eq cs a in
       let r' = lookup_eq cs r in
         (Inst (asm_Mem asm_Store32 r' (Addr a' w)),cs))
        | (asm_FP (FPLess r f1 f2)) ->
         (Inst (asm_FP (FPLess r f1 f2)),
           remove_eq cs r)
        | (asm_FP (FPLessEqual r f1 f2)) ->
         (Inst (asm_FP (FPLessEqual r f1 f2)),
           remove_eq cs r)
        | (asm_FP (FPEqual r f1 f2)) ->
         (Inst (asm_FP (FPEqual r f1 f2)),
           remove_eq cs r)
        | (asm_FP (FPMovToReg r1 r2 d):'a asm_inst) ->
         (Inst (asm_FP (FPMovToReg r1 r2 d)),
           remove_eqs cs [r1; r2])
        | (asm_FP (FPMovFromReg d r1 r2)) ->
         (let r1' = lookup_eq cs r1 in
         let r2' = lookup_eq cs r2 in
         let (r1'',r2'') = if r1' = r2' then (r1,r2) else (r1',r2')
           in
         (Inst (asm_FP (FPMovFromReg d r1'' r2'')),cs))
        | (asm_FP x) -> (Inst (asm_FP x),cs)
        | _2 -> ARB`;;

(* handle x := y by making x the new
  class representative of y.
  x must be guaranteed to not have to_eq *)
let set_eq_def = cake_define
  `set_eq cs x y =
   (if is_alloc_var x /\ is_alloc_var y then
     match
       (match sptree_lookup y (copy_state_to_eq cs) with
         NONE -> NONE | SOME c -> (if sptree_lookup c
           (copy_state_from_eq cs) = NONE then NONE else SOME c)) with
        NONE ->
       mk_copy_state (sptree_insert x (copy_state_next cs)
         (sptree_insert y (copy_state_next cs) (copy_state_to_eq cs)))
         (sptree_insert (copy_state_next cs) x (copy_state_from_eq cs))
         (copy_state_store_to_eq cs) (copy_state_next cs + 1) | SOME c
         ->
       mk_copy_state (sptree_insert x c (copy_state_to_eq cs))
         (sptree_insert c x (copy_state_from_eq cs))
         (copy_state_store_to_eq cs) (copy_state_next cs) else
     cs)`;;

(* Handle Store <- y
  If y has no equivalence class,
    create a singleton equivalence class for y
  Otherwise, reuse the existing class for y.
  Note: SSA ensures y is always an alloc_var, so the else branch is dead
    code.
*)
let set_store_eq_def = cake_define
  `set_store_eq cs s y =
   (if is_alloc_var y then
     match
       (match sptree_lookup y (copy_state_to_eq cs) with
         NONE -> NONE | SOME c -> (if sptree_lookup c
           (copy_state_from_eq cs) = NONE then NONE else SOME c)) with
       NONE ->
       mk_copy_state (sptree_insert y (copy_state_next cs)
         (copy_state_to_eq cs)) (sptree_insert (copy_state_next cs) y
         (copy_state_from_eq cs)) ((s,copy_state_next cs) ::
         copy_state_store_to_eq cs) (copy_state_next cs + 1) | SOME c ->
         copy_state_store_to_eq_fupd (K ((s,c) :: copy_state_store_to_eq
         cs))
       cs else empty_eq)`;;

let lookup_store_eq_def = cake_define
  `lookup_store_eq cs s =
   (match ALOOKUP (copy_state_store_to_eq cs) s with
     NONE -> NONE | SOME c ->
     (match sptree_lookup c (copy_state_from_eq cs) with
       NONE -> NONE | SOME v' -> SOME v'))`;;

(* conservatively merge two equivalence classes *)
let merge_eqs_def = cake_define
  `merge_eqs cs ds =
   mk_copy_state (inter_eq (copy_state_to_eq cs) (copy_state_to_eq
     ds)) (inter_eq (copy_state_from_eq cs) (copy_state_from_eq ds))
         (FILTER (\(s,c). ALOOKUP (copy_state_store_to_eq cs) s =
           SOME c /\
                         ALOOKUP (copy_state_store_to_eq ds) s =
                           SOME c) (copy_state_store_to_eq cs)) (MAX
                           (copy_state_next cs) (copy_state_next ds))`;;

(* shouldn't matter whether we put y or y' in set_eq? *)
let copy_prop_move_def = cake_define_list
  [`copy_prop_move [] cs = ([],cs)`;
   `copy_prop_move ((x,y) :: xs) cs =
        (let y' = lookup_eq cs y in
        let (ms,cs') = copy_prop_move xs cs in
        let cs'' = set_eq (remove_eq cs' x) x y in
        ((x,y') :: ms,cs''))`];;

let copy_prop_share_def = cake_define
  `copy_prop_share exp cs =
     (match exp with
     Var r -> Var (lookup_eq cs r) | (wordLang_Op Add [Var r; Const
       c]) ->
      wordLang_Op Add [Var (lookup_eq cs r); Const c] | _3 -> exp)`;;

let copy_prop_prog_def = cake_define
  `copy_prop_prog prog cs =
        match prog with
          (Skip:'a wordLang_prog) ->
       (Skip,cs)
        | (wordLang_Move pri xs) ->
       (let tt = MAP FST xs in let ss = MAP SND xs in
       if EVERY (\t. ~MEM t ss) tt then
         let (xs',cs') = copy_prop_move xs cs in
         (wordLang_Move pri xs',cs') else (wordLang_Move pri
           xs,empty_eq))
        | (Inst i) ->
       copy_prop_inst i cs
        | (Return v1 v2) ->
       (let v1' = lookup_eq cs v1 in
       let v2' = MAP (lookup_eq cs) v2 in
         (Return v1' v2',cs))
        | (Raise v) ->
       (let v' = lookup_eq cs v in
         (Raise v',cs))
        | (OpCurrHeap b dst src) ->
       (let src' = lookup_eq cs src in
       let src'' = if src' = dst then src else src' in
         (OpCurrHeap b dst src'',
            remove_eq cs dst))
        | Tick -> (Tick,cs)
        | (wordLang_MustTerminate p1) ->
       (let (p1',cs') = copy_prop_prog p1 cs in
       (wordLang_MustTerminate p1',cs'))
        | (Seq p1 p2) ->
        (let (q1,cs') = copy_prop_prog p1 cs in
        let (q2,cs'') = copy_prop_prog p2 cs' in
          (Seq q1 q2,cs''))
        | (If cmp r ri p1 p2) ->
        (let r' = lookup_eq cs r in
        let ri' = lookup_eq_imm cs ri in
        let (q1,cs') = copy_prop_prog p1 cs in
        let (q2,cs'') = copy_prop_prog p2 cs in
          (If cmp r' ri' q1 q2,
          merge_eqs cs' cs''))
        | (Set name exp) ->
       (match exp with
         Var n ->
         (let n' = lookup_eq cs n in
         (Set name (Var n'),set_store_eq cs name n)) | _4 -> (Set
           name exp,empty_eq))
        | (Get n name) ->
       (match lookup_store_eq cs name with
         NONE ->
           (Get n name,set_store_eq (remove_eq cs n) name n) | SOME v
             ->
         (if ~(v = n) then
         let (xs',cs') = copy_prop_move [(n,v)] cs in
           (wordLang_Move 0 xs',cs') else (Skip,cs)))
        | (Call ret dest args handler) ->
       (Call ret dest args handler,empty_eq)
        | (Alloc r live) ->
        (Alloc r live,empty_eq)
        | (StoreConsts a b c d ws) ->
         (StoreConsts a b c d ws,
           remove_eqs cs [a; b; c; d])
        | (LocValue r l1) ->
         (LocValue r l1,remove_eq cs r)
        | (Install r1 r2 r3 r4 live) ->
        (Install r1 r2 r3 r4 live,empty_eq)
        | (CodeBufferWrite r1 r2) ->
        (let r1' = lookup_eq cs r1 in
        let r2' = lookup_eq cs r2 in
        (CodeBufferWrite r1' r2',cs))
        | (DataBufferWrite r1 r2) ->
        (let r1' = lookup_eq cs r1 in
        let r2' = lookup_eq cs r2 in
        (DataBufferWrite r1' r2',cs))
        | (FFI i r1 r2 r3 r4 live) ->
       (FFI i r1 r2 r3 r4 live,empty_eq)
        | (wordLang_ShareInst op v exp) ->
       (let exp' = copy_prop_share exp cs in
       (wordLang_ShareInst op v exp',
         remove_eq cs v))
        | (Loop names c exit_names) ->
        (let (c',_5) = copy_prop_prog c empty_eq in
          (Loop names c' exit_names,empty_eq))
        | (Break k) -> (Break k,cs)
        | (Continue k) -> (Continue k,cs)
        | prog -> (prog,empty_eq)`;;

let copy_prop_def = cake_define
  `copy_prop (e:'a wordLang_prog) =
     FST (copy_prop_prog e empty_eq)`;;
