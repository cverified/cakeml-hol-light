(* ======================================================== *)
(*  word_simp: ported from HOL4's
    compiler/backend/word_simpScript.sml
    A definition theory, with 25 definitions and 7 theorems.  Needed
    by wordConvsProof.ml, word_cseProof.ml, word_simpProof.ml and
    word_to_word.ml.  *)
(* ======================================================== *)

(*
  This compiler phase performs lightweight optimisations on wordLang
  programs. It is in particular designed to clean up some awkward
  patterns that can be produced by the data_to_word compiler.
*)

needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_simp"
  ["asm"; "wordLang"];;

let _ = do_list hide_constant ["pmatch"];;

(* function that makes all Seq associate to the left *)

let SmartSeq_def = new_definition
  `SmartSeq p1 (p2:'a wordLang_prog) =
     (if p1 = wordLang_Skip then p2 else wordLang_Seq p1 p2)`;;

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let seq_assoc_def,seq_assoc_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x1)`
  [`Seq_assoc p1 other =
        match other with
          wordLang_Skip -> p1
        | (wordLang_Seq q1 q2) -> Seq_assoc (Seq_assoc p1 q1) q2
        | (wordLang_If v n r q1 q2) ->
        SmartSeq p1 (wordLang_If v n r (Seq_assoc wordLang_Skip q1)
          (Seq_assoc wordLang_Skip q2))
        | (wordLang_MustTerminate q) ->
        SmartSeq p1 (wordLang_MustTerminate (Seq_assoc wordLang_Skip
          q))
        | (wordLang_Call ret_prog dest args handler) ->
        SmartSeq p1 (wordLang_Call (match ret_prog with NONE -> NONE
          | SOME (x1,x2,q1,x3,x4) -> SOME (x1,x2,Seq_assoc
          wordLang_Skip q1,x3,x4))
          dest args
             (match handler with NONE -> NONE | SOME (y1,q2,y2,y3)
               -> SOME (y1,Seq_assoc wordLang_Skip q2,y2,y3)))
        | (wordLang_Loop names body exit_names) ->
        SmartSeq p1 (wordLang_Loop names (Seq_assoc wordLang_Skip
          body) exit_names)
        | other -> SmartSeq p1 other`];;

(* Seq_assoc_pmatch *)
let seq_assoc_pmatch = prove
 (`!p1 prog.
   Seq_assoc p1 prog =
   (match prog with wordLang_Skip -> p1 | (wordLang_Seq q1 q2) ->
     Seq_assoc (Seq_assoc p1 q1) q2 | (wordLang_If v n r q1 q2) ->
      SmartSeq p1 (wordLang_If v n r (Seq_assoc wordLang_Skip q1)
        (Seq_assoc wordLang_Skip q2)) | (wordLang_MustTerminate q) ->
      SmartSeq p1 (wordLang_MustTerminate (Seq_assoc wordLang_Skip
        q)) | (wordLang_Call ret_prog dest args handler) ->
      SmartSeq p1 (wordLang_Call (match ret_prog with NONE -> NONE |
        SOME (x1,x2,q1,x3,x4) -> SOME (x1,x2,Seq_assoc wordLang_Skip
        q1,x3,x4))
        dest args
           (match handler with NONE -> NONE | SOME (y1,q2,y2,y3) ->
             SOME (y1,Seq_assoc wordLang_Skip q2,y2,y3))) |
             (wordLang_Loop names body exit_names) ->
      SmartSeq p1 (wordLang_Loop names (Seq_assoc wordLang_Skip
        body) exit_names) | other -> SmartSeq p1 other)`,
  CHEAT_TAC);;

(* optimise certain consequtive If statements that arise from data-to-word

   If something (q1 ; n := X) (q2 ; n := Y) ;
   If (n == Z) p1 p2

   --> (in case X <> Y and Z == X)

   If something (q1 ; n := X ; p1) (q2 ; n := Y ; p2) ;

   similarly if Z == Y and X <> Y

*)

let word_simp_dest_Seq_def = new_definition
  `word_simp_dest_Seq p =
        match p with
          wordLang_Seq p1 p2 -> (p1,(p2:'a wordLang_prog))
        | p -> (wordLang_Skip,p)`;;

(* dest_Seq_pmatch *)
let word_simp_dest_Seq_pmatch = prove
 (`!p.
   word_simp_dest_Seq p =
   (match p with
     wordLang_Seq p1 p2 -> (p1,(p2:'a wordLang_prog)) | p ->
       (wordLang_Skip,p))`,
  CHEAT_TAC);;

let dest_If_def = new_definition
  `dest_If x1 =
        match x1 with
          wordLang_If x1 x2 x3 p1 p2 -> SOME (x1,x2,x3,p1,(p2:'a
            wordLang_prog))
        | _1 -> NONE`;;

let dest_If_pmatch = prove
 (`!p.
   dest_If p =
   (match p with
     wordLang_If x1 x2 x3 p1 p2 -> SOME (x1,x2,x3,p1,(p2:'a
       wordLang_prog)) | _2 -> NONE)`,
  CHEAT_TAC);;

let dest_If_Eq_Imm_def = new_definition
  `dest_If_Eq_Imm p =
     (match dest_If p with SOME (asm_Equal,n,Imm w,p1,p2) -> SOME
       (n,w,p1,p2) | _3 -> NONE)`;;

let dest_If_Eq_Imm_pmatch = prove
 (`!p.
   dest_If_Eq_Imm p =
     (match dest_If p with SOME (asm_Equal,n,Imm w,p1,p2) -> SOME
       (n,w,p1,p2) | _4 -> NONE)`,
  CHEAT_TAC);;

let dest_Seq_Assign_Const_def = new_definition
  `dest_Seq_Assign_Const n p =
     (let (p1,p2) = word_simp_dest_Seq p in
       match p2 with wordLang_Assign m (wordLang_Const w) -> (if m
         = n then SOME (p1,w) else NONE) | _5 -> NONE)`;;

let dest_Seq_Assign_Const_pmatch = prove
 (`!n p.
   dest_Seq_Assign_Const n p =
     (let (p1,p2) = word_simp_dest_Seq p in
       match p2 with wordLang_Assign m (wordLang_Const w) -> (if m
         = n then SOME (p1,w) else NONE) | _6 -> NONE)`,
  CHEAT_TAC);;

(* Constant folding and propagation optimization, e.g.

   x := 1;
   y := x + 4;
   z := y;

   becomes

   x := 1;
   y := 5;
   z := 5;

  Limitation: The current implementation forgets all constant values after a
  function call with a handler (for easier implementation and proofs). This is
  probably not difficult to improve, but would require some kind of theorem
  saying that a program does not change variables not mentioned in the program
  (because we cannot know beforehand/statically if the handler code is going to
  run, so we must throw away all variables mentioned in the handler).
 *)

let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let strip_const_def,strip_const_ind = define_wf
  `MEASURE (\x0. wordLang_exp_size1 (\x. 0) x0)`
  [`strip_const x1 =
        match x1 with
          [] -> SOME []
        | CONS (wordLang_Const w) cs ->
        (match strip_const cs with SOME ws -> SOME (CONS w ws) | _7
          -> NONE)
        | _8 -> NONE`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let const_fp_exp_def,const_fp_exp_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_exp_size (\x. 0) x0)`
  [`const_fp_exp e cs =
        match e with
          wordLang_Var v ->
        (match sptree_lookup v cs with SOME x -> wordLang_Const x |
          NONE -> wordLang_Var v)
        | (wordLang_Op op args) ->
        (let const_fp_args = MAP (\a. const_fp_exp a cs) args in
          match strip_const const_fp_args with SOME ws -> (match
            wordLang_word_op op ws with SOME w -> wordLang_Const w | _9
            -> wordLang_Op op (MAP wordLang_Const ws)) | _10 ->
            wordLang_Op op const_fp_args)
        | (wordLang_Shift sh e e1) ->
        (let const_fp_exp_e = const_fp_exp e cs in
        let const_fp_exp_e1 = const_fp_exp e1 cs in
          match (const_fp_exp_e,const_fp_exp_e1) with
            (wordLang_Const c,wordLang_Const c1) ->
                (match word_sh sh c (w2n c1) with SOME w ->
                  wordLang_Const w | _11 -> wordLang_Shift sh
                  (wordLang_Const c) (wordLang_Const c1)) | _12 ->
                  wordLang_Shift sh const_fp_exp_e const_fp_exp_e1)
        | e -> e`];;

let const_fp_move_cs_def,const_fp_move_cs_ind = define_rec
  [`const_fp_move_cs [] _14 cs = cs`;
   `const_fp_move_cs (CONS m ms) ocs ncs =
        (let v = FST m in
        let nncs =
          (match sptree_lookup (SND m) ocs with SOME c ->
              sptree_insert v c ncs | _15 -> sptree_delete v ncs) in
            const_fp_move_cs ms ocs nncs)`];;

let const_fp_inst_cs_def = new_definition
  `const_fp_inst_cs x1 cs =
        match x1 with
          asm_Const r _17 -> sptree_delete r cs
        | (asm_Arith (asm_Binop _18 r _19 _20)) -> sptree_delete r cs
        | (asm_Arith (asm_Shift _21 r _22 _23)) -> sptree_delete r cs
        | (asm_Arith (asm_AddCarry r1 _24 _25 r2)) -> sptree_delete
          r2 (sptree_delete r1 cs)
        | (asm_Arith (asm_AddOverflow r1 _26 _27 r2)) ->
          sptree_delete r2 (sptree_delete r1 cs)
        | (asm_Arith (asm_SubOverflow r1 _28 _29 r2)) ->
          sptree_delete r2 (sptree_delete r1 cs)
        | (asm_Arith (asm_LongMul r1 r2 _30 _31)) -> sptree_delete r1
          (sptree_delete r2 cs)
        | (asm_Arith (asm_LongDiv r1 r2 _32 _33 _34)) ->
          sptree_delete r1 (sptree_delete r2 cs)
        | (asm_Arith (asm_Div r1 _35 _36)) -> sptree_delete r1 cs
        | (asm_Mem asm_Load r _37) -> sptree_delete r cs
        | (asm_Mem asm_Load32 r _38) -> sptree_delete r cs
        | (asm_Mem asm_Load8 r _39) -> sptree_delete r cs
        | (asm_FP (FPLess r f1 f2)) -> sptree_delete r cs
        | (asm_FP (FPLessEqual r f1 f2)) -> sptree_delete r cs
        | (asm_FP (FPEqual r f1 f2)) -> sptree_delete r cs
        | ((asm_FP (FPMovToReg r1 r2 d)):'a asm_inst) ->
       (if dimindex (:'a) = 64 then sptree_delete r1 cs else
         sptree_delete r2 (sptree_delete r1 cs))
        | _40 -> cs`;;

let get_var_imm_cs_def = define_cases
  [`get_var_imm_cs (Reg r) cs = sptree_lookup r cs`;
   `get_var_imm_cs (Imm i) _41 = SOME i`];;

let is_gc_const_def = new_definition
  `is_gc_const c = ((c && (n2w 1)) = (n2w 0))`;;


let all_names_def = new_definition
  `all_names (n,m) = sptree_union n m`;;
add_simp all_names_def;;

(* HOL4 word_simpScript.sml:262: the overload delete_all, which the
   port expands *)

(* We only drop constants that can potentially be in registers *)
let drop_consts_def,drop_consts_ind = define_rec
  [`drop_consts cs [] = wordLang_Skip`;
   `drop_consts cs (CONS n ns) =
      (match sptree_lookup n cs with NONE -> drop_consts cs ns
          | SOME w -> SmartSeq (drop_consts cs ns) (wordLang_Assign
          n (wordLang_Const w)))`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let const_fp_loop_def,const_fp_loop_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_prog_size (\x. 0) x0)`
  [`const_fp_loop p cs =
        match p with
          wordLang_Move pri moves -> (wordLang_Move pri
            moves,const_fp_move_cs moves cs cs)
        | (wordLang_Inst i) -> (wordLang_Inst i,const_fp_inst_cs i
          cs)
        | (wordLang_Assign v e) ->
        (let const_fp_e = const_fp_exp e cs in
          match const_fp_e with wordLang_Const c -> (wordLang_Assign
            v const_fp_e,sptree_insert v c cs) | _42 ->
            (wordLang_Assign v const_fp_e,sptree_delete v cs))
        | (wordLang_Get v name) -> (wordLang_Get v
          name,sptree_delete v cs)
        | (wordLang_OpCurrHeap b v w) -> (wordLang_OpCurrHeap b v
          w,sptree_delete v cs)
        | (wordLang_MustTerminate p) ->
       (let (p',cs') = const_fp_loop p cs in
         (wordLang_MustTerminate p',cs'))
        | (wordLang_Seq p1 p2) ->
       (let (p1',cs') = const_fp_loop p1 cs in
       let (p2',cs'') = const_fp_loop p2 cs' in
         (wordLang_Seq p1' p2',cs''))
        | (wordLang_If cmp lhs rhs p1 p2) ->
       (match (sptree_lookup lhs cs,get_var_imm_cs rhs cs) with
         (SOME clhs,SOME crhs) ->
           (if asm_word_cmp cmp clhs crhs then const_fp_loop p1 cs
             else const_fp_loop p2 cs) | _43 -> (let (p1',p1cs) =
             const_fp_loop p1 cs in
                 let (p2',p2cs) = const_fp_loop p2 cs in
                  (wordLang_If cmp lhs rhs p1' p2',inter_eq p1cs
                    p2cs)))
        | (wordLang_Call ret dest args handler) ->
       (match ret with NONE -> (SmartSeq (drop_consts cs args)
         (wordLang_Call ret dest args handler),
                    filter_v is_gc_const cs) | SOME
                      (n,names,ret_handler,l1,l2) ->
           (if handler = NONE then
              (let cs' = (\n l. ITLIST sptree_delete n l) n
                (filter_v is_gc_const (inter cs (all_names names))) in
               let (ret_handler',cs'') = const_fp_loop ret_handler
                 cs' in
                 (SmartSeq (drop_consts cs args)
                   (wordLang_Call (SOME
                     (n,names,ret_handler',l1,l2)) dest args
                     handler),cs'')) else
              (SmartSeq (drop_consts cs args)
                (wordLang_Call ret dest args handler),LN)))
        | (wordLang_FFI x0 x1 x2 x3 x4 names) ->
       (SmartSeq (drop_consts cs [x1; x2; x3; x4]) (wordLang_FFI x0
         x1 x2 x3 x4 names),inter cs (all_names names))
        | (wordLang_LocValue v x3) -> (wordLang_LocValue v
          x3,sptree_delete v cs)
        | (wordLang_Alloc n names) ->
       (SmartSeq (drop_consts cs [n]) (wordLang_Alloc n
         names),filter_v is_gc_const (inter cs (all_names names)))
        | (wordLang_StoreConsts a b c d ws) -> (wordLang_StoreConsts
          a b c d ws,sptree_delete a (sptree_delete b (sptree_delete c
          (sptree_delete d cs))))
        | (wordLang_Install r1 r2 r3 r4 names) ->
       (SmartSeq (drop_consts cs [r1; r2; r3; r4])
         (wordLang_Install r1 r2 r3 r4 names),sptree_delete r1
           (filter_v is_gc_const (inter cs (all_names names))))
        | (wordLang_Store e v) ->
       (wordLang_Store (const_fp_exp e cs) v,cs)
        | (wordLang_ShareInst asm_Load v e) ->
       (wordLang_ShareInst asm_Load v (const_fp_exp e
         cs),sptree_delete v cs)
        | (wordLang_ShareInst asm_Load8 v e) ->
       (wordLang_ShareInst asm_Load8 v (const_fp_exp e
         cs),sptree_delete v cs)
        | (wordLang_ShareInst asm_Load16 v e) ->
       (wordLang_ShareInst asm_Load16 v (const_fp_exp e
         cs),sptree_delete v cs)
        | (wordLang_ShareInst asm_Load32 v e) ->
       (wordLang_ShareInst asm_Load32 v (const_fp_exp e
         cs),sptree_delete v cs)
        | (wordLang_ShareInst asm_Store v e) ->
       (wordLang_ShareInst asm_Store v (const_fp_exp e cs),cs)
        | (wordLang_ShareInst asm_Store8 v e) ->
       (wordLang_ShareInst asm_Store8 v (const_fp_exp e cs),cs)
        | (wordLang_ShareInst asm_Store16 v e) ->
       (wordLang_ShareInst asm_Store16 v (const_fp_exp e cs),cs)
        | (wordLang_ShareInst asm_Store32 v e) ->
       (wordLang_ShareInst asm_Store32 v (const_fp_exp e cs),cs)
        | (wordLang_Loop names body exit_names) ->
       (wordLang_Loop names (FST (const_fp_loop body LN))
         exit_names,LN)
        | p -> (p,cs)`];;

let const_fp_def = new_definition
  `const_fp p = FST (const_fp_loop p LN)`;;

(*
Optimise near-consecutive If/If pairs into a single If when there are only two
possible control-flow paths.

This case looks like:
  (if C then X else Y) ; Zs ; (if C2 then X2 else Y2)

Also, the number of intermediate Zs is small, (X ; Zs) guarantees either C2 or
not C2, and (Y ; Zs) guarantees the opposite. The second If can be removed at
the cost of duplicating the Zs.

The strategy here is (1) recognise the case, (2) expand the first If to cover
everything, hoisting copies of the second If into both branches and (3) re-run
the const_fp pass to simplify each branch down to a straight line.

This means the correctness follows straightforwardly from that of const_fp.

To recognise the case (1), step through Seq sequences which we expect to be
right-associated, and incrementally build up their left-associated variant
(which we will need eventually to pull things into the first If). Give up if
this takes too many steps (too many Zs). When an If is found, test-run the
const_fp pass to see if it would reduce the condition in the second If.
*)

let rewrite_duplicate_if_max_reassoc_def = new_definition
  `rewrite_duplicate_if_max_reassoc = 8`;;

let dest_Raise_num_pmatch_def = new_definition
  `dest_Raise_num p = (match p with wordLang_Raise n -> n | _44 -> 0)`;;

(* HOL4 word_simpScript.sml:378-379: a theorem that HOL4 states as
   the value of an ML expression: dest_Raise_num_def *)

let is_simple_pmatch_def = new_definition
  `is_simple p = (match p with wordLang_Tick -> T | wordLang_Skip ->
  T | wordLang_Move _45 _46 -> T | wordLang_Assign _47 _48 -> T | _49
  -> F)`;;

(* HOL4 word_simpScript.sml:390-391: a theorem that HOL4 states as
   the value of an ML expression: is_simple_def *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let try_if_hoist2_def,try_if_hoist2_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3,x4). (\n. n) x0)`
  [`try_if_hoist2 N p1 interm dummy' p2 = (if N = 0 then NONE else match
  p1 with wordLang_If cmp lhs rhs br1 br2 ->
       (let res1 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (wordLang_Seq (wordLang_Seq br1 interm) dummy')))) in
       if res1 = 0 then NONE else
       let res2 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (wordLang_Seq (wordLang_Seq br2 interm) dummy')))) in
       if ~(res1 + res2 = 3) then NONE else SOME (const_fp
         (wordLang_If cmp lhs rhs (wordLang_Seq (wordLang_Seq br1
         interm) p2)
           (wordLang_Seq (wordLang_Seq br2 interm) p2)))) |
             wordLang_Seq p3 p4 -> (
       match dest_If p4 with SOME (cmp,lhs,rhs,br1,br2) ->
       (let res1 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (wordLang_Seq (wordLang_Seq br1 interm) dummy')))) in
       if res1 = 0 then NONE else
       let res2 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (wordLang_Seq (wordLang_Seq br2 interm) dummy')))) in
       if ~(res1 + res2 = 3) then NONE else SOME (wordLang_Seq p3
         (const_fp (wordLang_If cmp lhs rhs (wordLang_Seq (wordLang_Seq
         br1 interm) p2)
           (wordLang_Seq (wordLang_Seq br2 interm) p2))))) | NONE ->
       (if is_simple p4 then try_if_hoist2 (N - 1) p3
         (wordLang_Seq p4 interm) dummy' p2 else NONE)) | _50 ->
         NONE)`];;

let try_if_hoist1_def = new_definition
  `try_if_hoist1 p1 p2 = (match dest_If p2 with NONE -> NONE | SOME
  (cmp,lhs,rhs,_51,_52) -> (
     let dummy' = wordLang_If cmp lhs rhs (wordLang_Raise 1)
       (wordLang_Raise 2) in
     try_if_hoist2 rewrite_duplicate_if_max_reassoc p1
       wordLang_Skip dummy' p2))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let simp_duplicate_if_def,simp_duplicate_if_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`simp_duplicate_if p = (match p with wordLang_MustTerminate q ->
  wordLang_MustTerminate (simp_duplicate_if q) | wordLang_Call ret_prog
  dest args handler ->
      wordLang_Call (match ret_prog with NONE -> NONE | SOME
        (x1,x2,q1,x3,x4) -> SOME (x1,x2,simp_duplicate_if q1,x3,x4))
        dest args
           (match handler with NONE -> NONE | SOME (y1,q2,y2,y3) ->
             SOME (y1,simp_duplicate_if q2,y2,y3)) | wordLang_If cmp
             lhs rhs br1 br2 ->
     wordLang_If cmp lhs rhs (simp_duplicate_if br1)
       (simp_duplicate_if br2) | wordLang_Seq p1 p2 -> (
     let p1x = simp_duplicate_if p1 in let
         p2x = simp_duplicate_if p2 in
     match try_if_hoist1 p1x p2x with NONE -> wordLang_Seq p1x p2x |
       SOME p3 -> Seq_assoc wordLang_Skip p3) | wordLang_Loop names
       body exit_names ->
     wordLang_Loop names (simp_duplicate_if body) exit_names |
       _53 -> p)`];;

(*Optimize pairs where one side is known to terminate due to a Raise or a Return
the flag is T when its known to halt and F otherwise

*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let push_out_if_aux_def,push_out_if_aux_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`// all of them together
   push_out_if_aux p = (match p with wordLang_MustTerminate q ->
     (match (push_out_if_aux q) with (c,b) ->
       (wordLang_MustTerminate c,b)) | wordLang_Return _54 _55 -> (p,T)
       | wordLang_Raise _56 -> (p,T) | wordLang_Call NONE _57 _58 _59
       -> (p,T) | wordLang_If cmp r1 ri c1 c2 -> (match
       (push_out_if_aux c1,push_out_if_aux c2) with ((c1',T),(c2',T))
       -> (wordLang_If cmp r1 ri c1' c2',T) | ((c1',F),(c2',T)) ->
       (wordLang_Seq (wordLang_If cmp r1 ri wordLang_Skip c2') c1',F) |
       ((c1',T),(c2',F)) -> (wordLang_Seq (wordLang_If cmp r1 ri c1'
       wordLang_Skip) c2',F) | ((c1',F),(c2',F)) -> (wordLang_If cmp r1
       ri c1' c2',F)) | wordLang_Seq c1 c2 -> (match (push_out_if_aux
       c1) with (c1',T) -> ((wordLang_Seq c1' c2),T) | (
                       // Don't have to bother as DCE will get rid of it
                       c1',F) ->
                       (match (push_out_if_aux c2) with (c2',b) ->
                         (wordLang_Seq c1' c2',b))) | wordLang_Loop
                         names body exit_names ->
     (wordLang_Loop names (FST (push_out_if_aux body))
       exit_names,F) | _60 -> (p,F))`];;

let push_out_if_def = new_definition
  `push_out_if p = FST (push_out_if_aux p)`;;


let word_simp_compile_exp_def = new_definition
  `word_simp_compile_exp (e:'a wordLang_prog) =
     (let e = Seq_assoc wordLang_Skip e in
     let e = const_fp e in
     let e = simp_duplicate_if e in
     let e = push_out_if e in
       e)`;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
