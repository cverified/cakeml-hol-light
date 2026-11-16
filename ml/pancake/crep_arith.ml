(* ======================================================== *)
(*  crep_arith: ported from HOL4's
    pancake/crep_arithScript.sml
    A definition theory, with 5 definitions and 2 theorems.  Needed
    by crep_to_loop.ml, data_to_word_memoryProof.ml,
    from_pancake32Prog.ml, from_pancake64Prog.ml and pan_passes.ml.  *)
(* ======================================================== *)

(*
  Simplification of arithmetic in crepLang.
*)

needs "pancake/crepLang.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "crep_arith"
  ["crepLang"];;

let dest_const_def = new_definition
  `crep_arith_dest_const x1 =
   match x1 with
     crep_Const w -> SOME w
   | _ -> NONE`;;

let dest_2exp_def,dest_2exp_ind = define_guess
  `dest_2exp n w = if w = (n2w 0) then NONE
     else if w = (n2w 1) then SOME n
     else if ~((w && (n2w 1)) = (n2w 0)) then NONE
     else dest_2exp (n + 1) (word_lsr w 1)`;;

(* [local] *)
let dest_2exp_lemma = prove
 (`!i w n. dest_2exp i w = SOME n ==>
   i <= n /\ w = word_lsl (n2w 1) (n - i)`,
  CHEAT_TAC);;

let dest_2exp_thm = prove
 (`dest_2exp 0 w = SOME n2 ==>
   w = word_lsl (n2w 1) n2`,
  CHEAT_TAC);;

let mul_const_def = new_definition
  `mul_const exp c = if c = (n2w 0) then crep_Const (n2w 0)
     else if c = (n2w 1) then exp
     else (match dest_2exp 0 c with NONE -> crep_Crepop crep_Mul [exp;
       crep_Const c]
       | SOME i -> crep_Shift Lsl exp (crep_Const (n2w i)))`;;

(* the termination relation that HOL4 gives is
     MEASURE (crep_exp_size (K 0))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let simp_exp_def,simp_exp_ind = define_guess
  `simp_exp exp =
     match exp with
       crep_Crepop op exps' ->
       (let exps' = MAP simp_exp exps' in
       match (op,exps') with (crep_Mul,[exp1; exp2]) -> (
           match (crep_arith_dest_const exp1,crep_arith_dest_const exp2)
             with (SOME c,SOME c2) -> crep_Const (c * c2)
           | (SOME c,_) -> mul_const exp2 c
           | (_,SOME c) -> mul_const exp1 c
           | _ -> crep_Crepop op exps')
       | _ -> crep_Crepop op exps')
     | crep_Load32 exp -> crep_Load32 (simp_exp exp)
     | crep_LoadByte exp -> crep_LoadByte (simp_exp exp)
     | crep_Load exp -> crep_Load (simp_exp exp)
     | crep_Op bop exps' -> crep_Op bop (MAP simp_exp exps')
     | crep_Cmp cmp exp1 exp2 -> crep_Cmp cmp (simp_exp exp1) (simp_exp
       exp2)
     | crep_Shift s exp1 exp2 -> crep_Shift s (simp_exp exp1) (simp_exp
       exp2)
     | exp -> exp`;;

let simp_prog_def,simp_prog_ind = define_guess
  `simp_prog p =
   match p with
     crep_Dec v exp p -> crep_Dec v (simp_exp exp) (simp_prog p)
   | crep_Assign v exp -> crep_Assign v (simp_exp exp)
   | crep_Store exp1 exp2 -> crep_Store (simp_exp exp1) (simp_exp exp2)
   | crep_Store32 exp1 exp2 -> crep_Store32 (simp_exp exp1) (simp_exp exp2)
   | crep_StoreByte exp1 exp2 -> crep_StoreByte (simp_exp exp1) (simp_exp
     exp2)
   | crep_StoreGlob g exp -> crep_StoreGlob g (simp_exp exp)
   | crep_Seq p1 p2 -> crep_Seq (simp_prog p1) (simp_prog p2)
   | crep_If exp p1 p2 -> crep_If (simp_exp exp) (simp_prog p1) (simp_prog
     p2)
   | crep_While exp p -> crep_While (simp_exp exp) (simp_prog p)
   | crep_Call call_type e exps' -> (
     let call_type2 = (match call_type with NONE -> NONE
       | SOME (rv,opt_handler) -> SOME (rv,(match opt_handler with NONE ->
         NONE
           | SOME (ix,ep) -> SOME (ix,simp_prog ep)))) in
     crep_Call call_type2 e (MAP simp_exp exps'))
   | crep_Return exp -> crep_Return (MAP simp_exp exp)
   | crep_ShMem op vn exp -> crep_ShMem op vn (simp_exp exp)
   | p -> p`;;

(* and the interface *)
let _ = unhide_overloads ();;
