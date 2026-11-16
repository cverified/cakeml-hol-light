(* ======================================================== *)
(*  loop_to_word: ported from HOL4's
    pancake/loop_to_wordScript.sml
    A definition theory, with 11 definitions and no theorems.
    Needed by from_pancake32Prog.ml, from_pancake64Prog.ml and
    pan_to_word.ml.  *)
(* ======================================================== *)

(*
  Compilation from loopLang to wordLang.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "pancake/loopLang.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "loop_to_word"
  ["backend_common"; "loopLang"; "wordLang"];;

let loop_to_word_find_var_def = new_definition
  `loop_to_word_find_var ctxt v =
     match sptree_lookup v ctxt with NONE -> 0
     | SOME n -> (n:num)`;;

let find_reg_imm_def = define_cases
  `(find_reg_imm ctxt (Imm w) = Imm w) /\
   (find_reg_imm ctxt (Reg n) = Reg (loop_to_word_find_var ctxt n))`;;

(* the termination relation that HOL4 gives is
     MEASURE (loop_exp_size (K 0) o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 loop_to_wordScript.sml:33-40: the tactic that proves the termination *)
let comp_exp_def,comp_exp_ind = define_guess
  `(comp_exp ctxt (loop_Const w) = word_Const w) /\
   (comp_exp ctxt (loop_Var n) = loop_Var (loop_to_word_find_var ctxt n)) /\
   (comp_exp ctxt (loop_Lookup m) = loop_Lookup (Temp m)) /\
   (comp_exp ctxt loop_BaseAddr = loop_Lookup CurrHeap) /\
   (comp_exp ctxt loop_TopAddr = loop_Op asm_Add [loop_Lookup CurrHeap;
    loop_Shift Lsl (loop_Lookup HeapLength) (loop_Const (n2w 1))]) /\
   (comp_exp ctxt (loop_Load exp) = loop_Load (comp_exp ctxt exp)) /\
   (comp_exp ctxt (loop_Shift s exp1 exp2) = loop_Shift s (comp_exp ctxt
    exp1) (comp_exp ctxt exp2)) /\
   (comp_exp ctxt (loop_Op op wexps) =
       let wexps = MAP (comp_exp ctxt) wexps in
       loop_Op op wexps)`;;

let toNumSet_def,toNumSet_ind = define_guess
  `(toNumSet [] = LN) /\
   (toNumSet (CONS n ns) = sptree_insert n one (toNumSet ns))`;;

let fromNumSet_def = new_definition
  `fromNumSet t = MAP FST (toAList t)`;;

let mk_new_cutset_def = new_definition
  `mk_new_cutset ctxt (l:1 spt) =
     sptree_insert 0 one (toNumSet (MAP (loop_to_word_find_var ctxt)
       (fromNumSet l)))`;;

(* the clauses in two quotations: a is (5 word) and num, which one quotation
   cannot typecheck *)
let loop_to_word_comp_def,loop_to_word_comp_ind = define_guess_clauses
  [`(loop_to_word_comp ctxt loop_Skip l = (word_Skip,l)) /\
    (loop_to_word_comp ctxt (loop_Assign n e) l =
         (loop_Assign (loop_to_word_find_var ctxt n) (comp_exp ctxt
             e),l)) /\
    (loop_to_word_comp ctxt (loop_Primitive lhss pop rhss) l =
         match pop with pan_AddCarry ->
           if LENGTH lhss = 2 /\ LENGTH rhss = 3 then
             let
               res = EL 0 lhss in let
               co = EL 1 lhss in let
               li = EL 0 rhss in let
               ri = EL 1 rhss in let
               ci = EL 2 rhss in let
               scratch_ci = 1 in let
               scratch_res = 3 in
               (loop_Seq (loop_Assign scratch_ci (loop_Var
                   (loop_to_word_find_var ctxt ci)))
               (loop_Seq (asm_Inst (asm_Arith (asm_AddCarry scratch_res
                              (loop_to_word_find_var ctxt li)
                              (loop_to_word_find_var ctxt ri)
                              scratch_ci)))
               (loop_Seq (loop_Assign (loop_to_word_find_var ctxt co)
                   (loop_Var scratch_ci))
                    (loop_Assign (loop_to_word_find_var ctxt res) (loop_Var
                        scratch_res)))),l)
           else (loop_Skip,l)) /\
    (loop_to_word_comp ctxt (loop_Arith arith) l =
         (match arith with
            LLongMul r1 r2 r3 r4 ->
            (asm_Inst (asm_Arith (asm_LongMul (loop_to_word_find_var ctxt
                r1) (loop_to_word_find_var ctxt r2)
                        (loop_to_word_find_var ctxt r3)
                            (loop_to_word_find_var ctxt r4))),l)
          | LLongDiv r1 r2 r3 r4 r5 ->
            (asm_Inst (asm_Arith (asm_LongDiv (loop_to_word_find_var ctxt
                r1) (loop_to_word_find_var ctxt r2)
                        (loop_to_word_find_var ctxt r3)
                            (loop_to_word_find_var ctxt r4)
                            (loop_to_word_find_var ctxt r5))),l)
          | LDiv r1 r2 r3 ->
            (asm_Inst (asm_Arith (asm_Div (loop_to_word_find_var ctxt
                r1) (loop_to_word_find_var ctxt r2) (loop_to_word_find_var
                ctxt r3))),l))) /\
    (loop_to_word_comp ctxt (loop_Store e v) l =
         (loop_Store (comp_exp ctxt e) (loop_to_word_find_var ctxt
             v),l)) /\
    (loop_to_word_comp ctxt (loop_SetGlobal a e) l =
         (word_Set (Temp a) (comp_exp ctxt e),l)) /\
    (loop_to_word_comp ctxt (loop_Seq p q) l =
        let (wp,l) = loop_to_word_comp ctxt p l in
         let (wq,l) = loop_to_word_comp ctxt q l in
           (loop_Seq wp wq,l)) /\
    (loop_to_word_comp ctxt (loop_If c n ri p q l1) l =
        let (wp,l) = loop_to_word_comp ctxt p l in
         let (wq,l) = loop_to_word_comp ctxt q l in
           (loop_Seq (word_If c (loop_to_word_find_var ctxt n)
               (find_reg_imm ctxt ri) wp wq) loop_Tick,l)) /\
    (loop_to_word_comp ctxt (loop_Loop l1 body l2) l =
        let (wbody,l) = loop_to_word_comp ctxt body l in
          (loop_Seq loop_Tick
             (loop_Seq (word_Loop (mk_new_cutset ctxt l1) wbody
                 (mk_new_cutset ctxt l2))
                  loop_Tick),l)) /\
    (loop_to_word_comp ctxt (loop_Break n) l = (loop_Break n,l)) /\
    (loop_to_word_comp ctxt (loop_Continue n) l = (loop_Continue n,l)) /\
    (loop_to_word_comp ctxt (loop_Raise v) l = (loop_Raise
    (loop_to_word_find_var ctxt v),l)) /\
    (loop_to_word_comp ctxt (loop_Return vs) l = (word_Return 0 (MAP
    (loop_to_word_find_var ctxt) vs),l)) /\
    (loop_to_word_comp ctxt loop_Tick l = (loop_Tick,l)) /\
    (loop_to_word_comp ctxt (loop_Mark p) l = loop_to_word_comp ctxt p l) /\
    (loop_to_word_comp ctxt loop_Fail l = (loop_Skip,l)) /\
    (loop_to_word_comp ctxt (loop_LocValue n m) l = (loop_LocValue
    (loop_to_word_find_var ctxt n) m,l)) /\
    (loop_to_word_comp ctxt (loop_Call ret dest args handler) l =
         let args = MAP (loop_to_word_find_var ctxt) args in
           match ret with NONE -> (
                   // tail-call
                   word_Call NONE dest (CONS 0 args) NONE,l)
           | SOME (vs,live) ->
             (let vs = MAP (loop_to_word_find_var ctxt) vs in
             let live = mk_new_cutset ctxt live in
             let new_l = (FST l,SND l + 1) in
               match handler with NONE -> (word_Call (SOME
                   (vs,(live,LN),loop_Skip,l)) dest args NONE,new_l)
               | SOME (n,p1,p2,_) ->
                  let (p1,l1) = loop_to_word_comp ctxt p1 new_l in
                  let (p2,l1) = loop_to_word_comp ctxt p2 l1 in
                  let new_l = (FST l1,SND l1 + 1) in
                    (loop_Seq (loop_Call (SOME (vs,(live,LN),p2,l)) dest
                        args
                       (SOME (loop_to_word_find_var ctxt n,p1,l1)))
                           loop_Tick,new_l))) /\
    (loop_to_word_comp ctxt (loop_FFI f ptr1 len1 ptr2 len2 live) l =
          let live = mk_new_cutset ctxt live in
            (loop_FFI f (loop_to_word_find_var ctxt ptr1)
                (loop_to_word_find_var ctxt len1)
                   (loop_to_word_find_var ctxt ptr2)
                       (loop_to_word_find_var ctxt len2) (live,LN),l)) /\
    (loop_to_word_comp ctxt (loop_ShMem memop n e) l =
          (word_ShareInst memop (loop_to_word_find_var ctxt n)
              (comp_exp ctxt e),l))`;
   `(loop_to_word_comp ctxt (loop_Load32 a v) l =
         (asm_Inst (asm_Mem asm_Load32 (loop_to_word_find_var ctxt v)
                (Addr (loop_to_word_find_var ctxt a) (n2w 0))),l)) /\
    (loop_to_word_comp ctxt (loop_LoadByte a v) l =
         (asm_Inst (asm_Mem asm_Load8 (loop_to_word_find_var ctxt v)
                (Addr (loop_to_word_find_var ctxt a) (n2w 0))),l)) /\
    (loop_to_word_comp ctxt (loop_Store32 a v) l =
         (asm_Inst (asm_Mem asm_Store32 (loop_to_word_find_var ctxt v)
                (Addr (loop_to_word_find_var ctxt a) (n2w 0))),l)) /\
    (loop_to_word_comp ctxt (loop_StoreByte a v) l =
         (asm_Inst (asm_Mem asm_Store8 (loop_to_word_find_var ctxt v)
                (Addr (loop_to_word_find_var ctxt a) (n2w 0))),l))`];;

let make_ctxt_def,make_ctxt_ind = define_guess
  `(make_ctxt n [] l = l) /\
   (make_ctxt n (CONS x xs) l = make_ctxt (n + (2:num)) xs (sptree_insert
    x n l))`;;

(*
  acc_vars body LN: accumulates the assigned variable with the given num_set
  The main function below is make_ctxt, we do the difference so that we do not
  replicate the parameters (variable names) that we are providing with the
  exsiting assigned variables present in the body of the program already
*)

let loop_to_word_comp_func_def = new_definition
  `loop_to_word_comp_func name params' body =
     let vs = fromNumSet (difference (acc_vars body LN) (toNumSet params'))
       in
     let ctxt = make_ctxt 2 (APPEND params' vs) LN in
       FST (loop_to_word_comp ctxt body (name,2))`;;

let loop_to_word_compile_prog_def = new_definition
  `loop_to_word_compile_prog p = MAP (\(name,params',body).
                          (name,LENGTH params' + 1,loop_to_word_comp_func
                            name params' body)) p`;;

let loop_to_word_compile_def = new_definition
  `loop_to_word_compile p = loop_to_word_compile_prog p`;;

(* and the interface *)
let _ = unhide_overloads ();;
