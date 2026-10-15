(* ======================================================== *)
(*  word_simp: ported from HOL4's
    compiler/backend/word_simpScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase performs lightweight optimisations on wordLang
  programs. It is in particular designed to clean up some awkward
  patterns that can be produced by the data_to_word compiler.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/comparison.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* function that makes all Seq associate to the left *)

let SmartSeq_def = cake_define
  `SmartSeq p1 (p2:'a wordLang_prog) =
     (if p1 = Skip then p2 else Seq p1 p2)`;;

let seq_assoc_def = cake_define
  `Seq_assoc p1 other =
        match other with
          wordLang_Skip -> p1
        | (Seq q1 q2) -> Seq_assoc (Seq_assoc p1 q1) q2
        | (If v n r q1 q2) ->
        SmartSeq p1 (If v n r (Seq_assoc Skip q1) (Seq_assoc Skip
          q2))
        | (wordLang_MustTerminate q) ->
        SmartSeq p1 (wordLang_MustTerminate (Seq_assoc Skip q))
        | (Call ret_prog dest args handler) ->
        SmartSeq p1 (Call (match ret_prog with NONE -> NONE | SOME
          (x1,x2,q1,x3,x4) -> SOME (x1,x2,Seq_assoc Skip q1,x3,x4))
          dest args
             (match handler with NONE -> NONE | SOME (y1,q2,y2,y3) ->
               SOME (y1,Seq_assoc Skip q2,y2,y3)))
        | (Loop names body exit_names) ->
        SmartSeq p1 (Loop names (Seq_assoc Skip body) exit_names)
        | other -> SmartSeq p1 other`;;

(* optimise certain consequtive If statements that arise from
   data-to-word

   If something (q1 ; n := X) (q2 ; n := Y) ;
   If (n == Z) p1 p2

   --> (in case X <> Y and Z == X)

   If something (q1 ; n := X ; p1) (q2 ; n := Y ; p2) ;

   similarly if Z == Y and X <> Y

*)

let dest_Seq_def = cake_define
  `word_simp_dest_Seq p =
        match p with
          wordLang_Seq p1 p2 -> (p1,(p2:'a wordLang_prog))
        | p -> (Skip,p)`;;
hol4_overload "dest_Seq" "word_simp_dest_Seq";;

let dest_If_def = cake_define
  `dest_If x1 =
        match x1 with
          wordLang_If x1 x2 x3 p1 p2 -> SOME (x1,x2,x3,p1,(p2:'a
            wordLang_prog))
        | _1 -> NONE`;;

let dest_If_Eq_Imm_def = cake_define
  `dest_If_Eq_Imm p =
     (match dest_If p with SOME (Equal,n,Imm w,p1,p2) -> SOME
       (n,w,p1,p2) | _2 -> NONE)`;;

let dest_Seq_Assign_Const_def = cake_define
  `dest_Seq_Assign_Const n p =
     (let (p1,p2) = word_simp_dest_Seq p in
       match p2 with wordLang_Assign m (Const w) -> (if m = n then
         SOME (p1,w) else NONE) | _3 -> NONE)`;;

(* Constant folding and propagation optimization, e.g.

   x := 1;
   y := x + 4;
   z := y;

   becomes

   x := 1;
   y := 5;
   z := 5;

  Limitation: The current implementation forgets all constant values
    after a
  function call with a handler (for easier implementation and proofs).
    This is
  probably not difficult to improve, but would require some kind of
    theorem
  saying that a program does not change variables not mentioned in the
    program
  (because we cannot know beforehand/statically if the handler code is
    going to
  run, so we must throw away all variables mentioned in the handler).
 *)

let strip_const_def = cake_define
  `strip_const x1 =
        match x1 with
          [] -> SOME []
        | (Const w :: cs) ->
        (match strip_const cs with SOME ws -> SOME (w :: ws) | _4 ->
          NONE)
        | _5 -> NONE`;;

let const_fp_exp_def = cake_define
  `const_fp_exp e cs =
        match e with
          wordLang_Var v ->
        (match sptree_lookup v cs with SOME x -> Const x | NONE ->
          Var v)
        | (wordLang_Op op args) ->
        (let const_fp_args = MAP (\a. const_fp_exp a cs) args in
          match strip_const const_fp_args with SOME ws -> (match
            wordLang_word_op op ws with SOME w -> Const w | _6 ->
            wordLang_Op op (MAP Const ws)) | _7 -> wordLang_Op op
            const_fp_args)
        | (Shift sh e e1) ->
        (let const_fp_exp_e = const_fp_exp e cs in
        let const_fp_exp_e1 = const_fp_exp e1 cs in
          match (const_fp_exp_e,const_fp_exp_e1) with (Const c,Const
            c1) ->
                (match word_sh sh c (w2n c1) with SOME w -> Const w |
                  _8 -> Shift sh (Const c) (Const c1)) | _9 -> Shift sh
                  const_fp_exp_e const_fp_exp_e1)
        | e -> e`;;

let const_fp_move_cs_def = cake_define_list
  [`const_fp_move_cs [] _11 cs = cs`;
   `const_fp_move_cs (m :: ms) ocs ncs =
        (let v = FST m in
        let nncs =
          (match sptree_lookup (SND m) ocs with SOME c ->
            sptree_insert v c ncs | _12 -> sptree_delete v ncs) in
            const_fp_move_cs ms ocs nncs)`];;

let const_fp_inst_cs_def = cake_define
  `const_fp_inst_cs x1 cs =
        match x1 with
          asm_Const r _14 -> sptree_delete r cs
        | (Arith (asm_Binop _15 r _16 _17)) -> sptree_delete r cs
        | (Arith (Shift _18 r _19 _20)) -> sptree_delete r cs
        | (Arith (asm_AddCarry r1 _21 _22 r2)) -> sptree_delete r2
          (sptree_delete r1 cs)
        | (Arith (asm_AddOverflow r1 _23 _24 r2)) -> sptree_delete r2
          (sptree_delete r1 cs)
        | (Arith (asm_SubOverflow r1 _25 _26 r2)) -> sptree_delete r2
          (sptree_delete r1 cs)
        | (Arith (asm_LongMul r1 r2 _27 _28)) -> sptree_delete r1
          (sptree_delete r2 cs)
        | (Arith (asm_LongDiv r1 r2 _29 _30 _31)) -> sptree_delete r1
          (sptree_delete r2 cs)
        | (Arith (Div r1 _32 _33)) -> sptree_delete r1 cs
        | (asm_Mem Load r _34) -> sptree_delete r cs
        | (asm_Mem asm_Load32 r _35) -> sptree_delete r cs
        | (asm_Mem asm_Load8 r _36) -> sptree_delete r cs
        | (asm_FP (FPLess r f1 f2)) -> sptree_delete r cs
        | (asm_FP (FPLessEqual r f1 f2)) -> sptree_delete r cs
        | (asm_FP (FPEqual r f1 f2)) -> sptree_delete r cs
        | ((asm_FP (FPMovToReg r1 r2 d)):'a asm_inst) ->
       (if dimindex (:'a) = 64 then sptree_delete r1 cs else
         sptree_delete r2 (sptree_delete r1 cs))
        | _37 -> cs`;;

let get_var_imm_cs_def = cake_define_list
  [`get_var_imm_cs (Reg r) cs = sptree_lookup r cs`;
   `get_var_imm_cs (Imm i) _38 = SOME i`];;

let is_gc_const_def = cake_define
  `is_gc_const c = ((c && (n2w 1)) = (n2w 0))`;;


let all_names_def = cake_define
  `all_names (n,m) = sptree_union n m`;;

(* HOL4 overload (expanded in the port):
     delete_all = λn l. FOLDR delete l n *)

(* We only drop constants that can potentially be in registers *)
let drop_consts_def = cake_define_list
  [`drop_consts cs [] = Skip`;
   `drop_consts cs (n :: ns) =
      (match sptree_lookup n cs with NONE -> drop_consts cs ns
        | SOME w -> SmartSeq (drop_consts cs ns) (wordLang_Assign n
        (Const w)))`];;

let const_fp_loop_def = cake_define
  `const_fp_loop p cs =
        match p with
          wordLang_Move pri moves -> (wordLang_Move pri
            moves,const_fp_move_cs moves cs cs)
        | (Inst i) -> (Inst i,const_fp_inst_cs i cs)
        | (wordLang_Assign v e) ->
        (let const_fp_e = const_fp_exp e cs in
          match const_fp_e with Const c -> (wordLang_Assign v
            const_fp_e,sptree_insert v c cs) | _39 -> (wordLang_Assign v
            const_fp_e,sptree_delete v cs))
        | (Get v name) -> (Get v name,sptree_delete v cs)
        | (OpCurrHeap b v w) -> (OpCurrHeap b v w,sptree_delete v cs)
        | (wordLang_MustTerminate p) ->
       (let (p',cs') = const_fp_loop p cs in
         (wordLang_MustTerminate p',cs'))
        | (Seq p1 p2) ->
       (let (p1',cs') = const_fp_loop p1 cs in
       let (p2',cs'') = const_fp_loop p2 cs' in
         (Seq p1' p2',cs''))
        | (wordLang_If cmp lhs rhs p1 p2) ->
       (match (sptree_lookup lhs cs,get_var_imm_cs rhs cs) with (SOME
         clhs,SOME crhs) ->
           (if asm_word_cmp cmp clhs crhs then const_fp_loop p1 cs
             else const_fp_loop p2 cs) | _40 -> (let (p1',p1cs) =
             const_fp_loop p1 cs in
                 let (p2',p2cs) = const_fp_loop p2 cs in
                  (wordLang_If cmp lhs rhs p1' p2',inter_eq p1cs
                    p2cs)))
        | (Call ret dest args handler) ->
       (match ret with NONE -> (SmartSeq (drop_consts cs args) (Call
         ret dest args handler),
                    filter_v is_gc_const cs) | SOME
                      (n,names,ret_handler,l1,l2) ->
           (if handler = NONE then
              (let cs' = (\n l. ITLIST sptree_delete n l) n (filter_v
                is_gc_const (inter cs (all_names names))) in
               let (ret_handler',cs'') = const_fp_loop ret_handler
                 cs' in
                 (SmartSeq (drop_consts cs args)
                   (Call (SOME (n,names,ret_handler',l1,l2)) dest
                     args handler),cs'')) else
              (SmartSeq (drop_consts cs args)
                (Call ret dest args handler),LN)))
        | (FFI x0 x1 x2 x3 x4 names) ->
       (SmartSeq (drop_consts cs [x1; x2; x3; x4]) (FFI x0 x1 x2 x3
         x4 names),inter cs (all_names names))
        | (LocValue v x3) -> (LocValue v x3,sptree_delete v cs)
        | (Alloc n names) ->
       (SmartSeq (drop_consts cs [n]) (Alloc n names),filter_v
         is_gc_const (inter cs (all_names names)))
        | (StoreConsts a b c d ws) -> (StoreConsts a b c d
          ws,sptree_delete a (sptree_delete b (sptree_delete c
          (sptree_delete d cs))))
        | (Install r1 r2 r3 r4 names) ->
       (SmartSeq (drop_consts cs [r1; r2; r3; r4])
         (Install r1 r2 r3 r4 names),sptree_delete r1 (filter_v
           is_gc_const (inter cs (all_names names))))
        | (Store e v) ->
       (Store (const_fp_exp e cs) v,cs)
        | (wordLang_ShareInst Load v e) ->
       (wordLang_ShareInst Load v (const_fp_exp e cs),sptree_delete v
         cs)
        | (wordLang_ShareInst asm_Load8 v e) ->
       (wordLang_ShareInst asm_Load8 v (const_fp_exp e
         cs),sptree_delete v cs)
        | (wordLang_ShareInst asm_Load16 v e) ->
       (wordLang_ShareInst asm_Load16 v (const_fp_exp e
         cs),sptree_delete v cs)
        | (wordLang_ShareInst asm_Load32 v e) ->
       (wordLang_ShareInst asm_Load32 v (const_fp_exp e
         cs),sptree_delete v cs)
        | (wordLang_ShareInst Store v e) ->
       (wordLang_ShareInst Store v (const_fp_exp e cs),cs)
        | (wordLang_ShareInst asm_Store8 v e) ->
       (wordLang_ShareInst asm_Store8 v (const_fp_exp e cs),cs)
        | (wordLang_ShareInst asm_Store16 v e) ->
       (wordLang_ShareInst asm_Store16 v (const_fp_exp e cs),cs)
        | (wordLang_ShareInst asm_Store32 v e) ->
       (wordLang_ShareInst asm_Store32 v (const_fp_exp e cs),cs)
        | (Loop names body exit_names) ->
       (Loop names (FST (const_fp_loop body LN)) exit_names,LN)
        | p -> (p,cs)`;;

let const_fp_def = cake_define
  `const_fp p = FST (const_fp_loop p LN)`;;

(*
Optimise near-consecutive If/If pairs into a single If when there are
  only two
possible control-flow paths.

This case looks like:
  (if C then X else Y) ; Zs ; (if C2 then X2 else Y2)

Also, the number of intermediate Zs is small, (X ; Zs) guarantees either
  C2 or
not C2, and (Y ; Zs) guarantees the opposite. The second If can be
  removed at
the cost of duplicating the Zs.

The strategy here is (1) recognise the case, (2) expand the first If to
  cover
everything, hoisting copies of the second If into both branches and (3)
  re-run
the const_fp pass to simplify each branch down to a straight line.

This means the correctness follows straightforwardly from that of
  const_fp.

To recognise the case (1), step through Seq sequences which we expect to
  be
right-associated, and incrementally build up their left-associated
  variant
(which we will need eventually to pull things into the first If). Give
  up if
this takes too many steps (too many Zs). When an If is found, test-run
  the
const_fp pass to see if it would reduce the condition in the second If.
*)

let rewrite_duplicate_if_max_reassoc_def = cake_define
  `rewrite_duplicate_if_max_reassoc = 8`;;

let dest_Raise_num_pmatch_def = cake_define
  `dest_Raise_num p = (match p with wordLang_Raise n -> n | _41 -> 0)`;;

let is_simple_pmatch_def = cake_define
  `is_simple p = (match p with Tick -> T | Skip -> T | wordLang_Move
  _42 _43 -> T | wordLang_Assign _44 _45 -> T | _46 -> F)`;;

let try_if_hoist2_def = cake_define
  `try_if_hoist2 N p1 interm dummy' p2 = (if N = 0 then NONE else match
  p1 with wordLang_If cmp lhs rhs br1 br2 ->
       (let res1 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (Seq (Seq br1 interm) dummy')))) in
       if res1 = 0 then NONE else
       let res2 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (Seq (Seq br2 interm) dummy')))) in
       if ~(res1 + res2 = 3) then NONE else SOME (const_fp (If cmp
         lhs rhs (Seq (Seq br1 interm) p2)
           (Seq (Seq br2 interm) p2)))) | Seq p3 p4 -> (
       match dest_If p4 with SOME (cmp,lhs,rhs,br1,br2) ->
       (let res1 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (Seq (Seq br1 interm) dummy')))) in
       if res1 = 0 then NONE else
       let res2 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (Seq (Seq br2 interm) dummy')))) in
       if ~(res1 + res2 = 3) then NONE else SOME (Seq p3 (const_fp
         (If cmp lhs rhs (Seq (Seq br1 interm) p2)
           (Seq (Seq br2 interm) p2))))) | NONE ->
       (if is_simple p4 then try_if_hoist2 (N - 1) p3 (Seq p4
         interm) dummy' p2 else NONE)) | _47 -> NONE)`;;

let try_if_hoist1_def = cake_define
  `try_if_hoist1 p1 p2 = (match dest_If p2 with NONE -> NONE | SOME
  (cmp,lhs,rhs,_48,_49) -> (
     let dummy' = wordLang_If cmp lhs rhs (Raise 1) (Raise 2) in
     try_if_hoist2 rewrite_duplicate_if_max_reassoc p1 Skip dummy'
       p2))`;;

let simp_duplicate_if_def = cake_define
  `simp_duplicate_if p = (match p with wordLang_MustTerminate q ->
  wordLang_MustTerminate (simp_duplicate_if q) | Call ret_prog dest args
  handler ->
      Call (match ret_prog with NONE -> NONE | SOME (x1,x2,q1,x3,x4)
        -> SOME (x1,x2,simp_duplicate_if q1,x3,x4))
        dest args
           (match handler with NONE -> NONE | SOME (y1,q2,y2,y3) ->
             SOME (y1,simp_duplicate_if q2,y2,y3)) | If cmp lhs rhs br1
             br2 ->
     If cmp lhs rhs (simp_duplicate_if br1) (simp_duplicate_if br2) |
       Seq p1 p2 -> (
     let p1x = simp_duplicate_if p1 in let
         p2x = simp_duplicate_if p2 in
     match try_if_hoist1 p1x p2x with NONE -> Seq p1x p2x | SOME p3
       -> Seq_assoc Skip p3) | Loop names body exit_names ->
     Loop names (simp_duplicate_if body) exit_names | _50 -> p)`;;

(*Optimize pairs where one side is known to terminate due to a Raise or
   a Return
the flag is T when its known to halt and F otherwise

*)
let push_out_if_aux_def = cake_define
  `push_out_if_aux p = (match p with wordLang_MustTerminate q ->
     (match (push_out_if_aux q) with (c,b) -> (wordLang_MustTerminate
       c,b)) | Return _51 _52 -> (p,T) | Raise _53 -> (p,T) | Call NONE
       _54 _55 _56 -> (p,T) | If cmp r1 ri c1 c2 -> (match
       (push_out_if_aux c1,push_out_if_aux c2) with ((c1',T),(c2',T)) ->
       (If cmp r1 ri c1' c2',T) | ((c1',F),(c2',T)) -> (Seq (If cmp r1
       ri Skip c2') c1',F) | ((c1',T),(c2',F)) -> (Seq (If cmp r1 ri c1'
       Skip) c2',F) | ((c1',F),(c2',F)) -> (If cmp r1 ri c1' c2',F)) |
       Seq c1 c2 -> (match (push_out_if_aux c1) with (c1',T) -> ((Seq
       c1' c2),T) | (c1',F) ->
                       (match (push_out_if_aux c2) with (c2',b) ->
                         (Seq c1' c2',b))) | Loop names body exit_names
                         ->
     (Loop names (FST (push_out_if_aux body)) exit_names,F) | _57
       -> (p,F))`;;

let push_out_if_def = cake_define
  `push_out_if p = FST (push_out_if_aux p)`;;


let compile_exp_def = cake_define
  `word_simp_compile_exp (e:'a wordLang_prog) =
     (let e = Seq_assoc Skip e in
     let e = const_fp e in
     let e = simp_duplicate_if e in
     let e = push_out_if e in
       e)`;;
hol4_overload "compile_exp" "word_simp_compile_exp";;
