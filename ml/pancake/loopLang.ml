(* ======================================================== *)
(*  loopLang: ported from HOL4's
    pancake/loopLangScript.sml
    A definition theory, with 4 definitions, 3 datatypes and 1
    theorem.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  loopLang intermediate language
*)

needs "compiler/backend/backend_common.ml";;
(* for overloading shift operation *)
needs "compiler/encoders/asm/asm.ml";;
(* for importing binop and cmp *)
needs "lib/sptree.ml";;
(* for num_set *)
needs "pancake/panLang.ml";;
(* for primop *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "loopLang"
  ["asm"; "backend_common"; "panLang"];;

new_type_abbrev("loop_shift",`:ast_shift`);;

let loop_exp_INDUCT,loop_exp_RECURSION = define_datatype
  "loop_exp =
     loop_Const ('a word)
   | loop_Var num
   | loop_Lookup (5 word)
   | loop_Load loop_exp
   | loop_Op asm_binop (loop_exp list)
   | loop_Shift loop_shift loop_exp loop_exp
   | loop_BaseAddr
   | loop_TopAddr";;

let loop_arith_INDUCT,loop_arith_RECURSION = define_datatype
  "loop_arith =
     LLongMul num num num num
   | LLongDiv num num num num num
   | LDiv num num num";;

let loop_prog_INDUCT,loop_prog_RECURSION = define_datatype
  "loop_prog =
     loop_Skip
   | loop_Assign num ('a loop_exp)
     // dest, source
   | loop_Primitive (num list) primop (num list)
   | loop_Arith loop_arith
   | loop_Store ('a loop_exp) num
     // dest, source
   | loop_SetGlobal (5 word) ('a loop_exp)
     // dest, source
   | loop_Load32 num num
     // TODISC: have removed imm, why num num?
   | loop_LoadByte num num
     // TODISC: have removed imm, why num num?
   | loop_Store32 num num
   | loop_StoreByte num num
   | loop_Seq loop_prog loop_prog
   | loop_If cmp num ('a asm_reg_imm) loop_prog loop_prog misc_num_set
   | loop_Loop misc_num_set loop_prog misc_num_set
     // names in, body, names out
   | loop_Break num
   | loop_Continue num
   | loop_Raise num
   | loop_Return (num list)
   | loop_ShMem memop num ('a loop_exp)
   | loop_Tick
   | loop_Mark loop_prog
   | loop_Fail
   | loop_LocValue num num
     // assign v1 := Loc v2 0
   | loop_Call ((num list#misc_num_set) option) (num option) (num list)
       ((num#loop_prog#loop_prog#misc_num_set) option)
     // return var
     // target of call
     // arguments
     // var to store exception,
     // exception-handler code,
     // normal-return handler code,
     // live vars after call
   | loop_FFI mlstring num num num num misc_num_set
     // FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set
  ";;

(* HOL4 loopLangScript.sml:64-70: a theorem whose statement the port cannot
   state yet: MEM_IMP_exp_size *)

let loop_nested_seq_def,loop_nested_seq_ind = define_guess
  `(loop_nested_seq [] = loop_Skip) /\
   (loop_nested_seq (CONS e es) = loop_Seq e (loop_nested_seq es))`;;

(* the termination relation that HOL4 gives is
     MEASURE (\e. loop_exp_size ARB e)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 loopLangScript.sml:86-92: the tactic that proves the termination *)
let locals_touched_def,locals_touched_ind = define_guess
  `(locals_touched (loop_Const w) = []) /\
   (locals_touched (loop_Var v) = [v]) /\
   (locals_touched (loop_Lookup name) = []) /\
   (locals_touched (loop_Load addr) = locals_touched addr) /\
   (locals_touched (loop_Op op wexps) = FLAT (MAP locals_touched wexps)) /\
   (locals_touched (loop_Shift sh wexp1 wexp2) = APPEND (locals_touched
    wexp1) (locals_touched wexp2)) /\
   (locals_touched loop_BaseAddr = []) /\
   (locals_touched loop_TopAddr = [])`;;

let loop_assigned_vars_def,loop_assigned_vars_ind = define_guess
  `loop_assigned_vars x1 =
     match x1 with
       loop_Skip -> []
     | loop_Assign n e -> [n]
     | loop_Primitive lhss pop rhss -> lhss
     | loop_Arith arith ->
      (match arith with
        LLongMul v1 v2 v3 v4 -> [v1; v2]
      | LLongDiv v1 v2 v3 v4 v5 -> [v1; v2]
      | LDiv v1 v2 v3 -> [v1])
     | loop_Load32 n m -> [m]
     | loop_LoadByte n m -> [m]
     | loop_Seq p q -> APPEND (loop_assigned_vars p) (loop_assigned_vars q)
     | loop_If cmp n r p q ns -> APPEND (loop_assigned_vars p)
       (loop_assigned_vars q)
     | loop_LocValue n m -> [n]
     | loop_ShMem op n e -> [n]
     | loop_Mark p -> loop_assigned_vars p
     | loop_Loop _ p _ -> loop_assigned_vars p
     | loop_Call NONE _ _ _ -> []
     | loop_Call (SOME (ns,_)) _ _ NONE -> ns
     | loop_Call (SOME (ns,_)) _ _ (SOME (m,p,q,_)) -> APPEND (APPEND ns
       (CONS m (loop_assigned_vars p))) (loop_assigned_vars q)
     | _ -> []`;;

(* the clauses in two quotations: v is num and (num list), which one
   quotation cannot typecheck *)
let acc_vars_def,acc_vars_ind = define_guess_clauses
  [`(acc_vars (loop_Seq p1 p2) (l:1 spt) = ((acc_vars p1 (acc_vars p2 l)):1
    spt)) /\
    (acc_vars (loop_Break _) (l:1 spt) = (l:1 spt)) /\
    (acc_vars (loop_Continue _) (l:1 spt) = ((l):1 spt)) /\
    (acc_vars (loop_Loop l1 body l2) (l:1 spt) = ((acc_vars body l):1 spt)) /\
    (acc_vars (loop_If x1 x2 x3 p1 p2 l1) (l:1 spt) = ((acc_vars p1
    (acc_vars p2 l)):1 spt)) /\
    (acc_vars (loop_Arith arith) (l:1 spt) =
       ((match arith with
         LLongMul v1 v2 v3 v4 -> sptree_insert v1 one (sptree_insert v2 one
             l)
       | LLongDiv v1 v2 v3 v4 v5 -> sptree_insert v1 one (sptree_insert v2
           one l)
       | LDiv v1 v2 v3 -> sptree_insert v1 one l):1 spt)) /\
    (acc_vars (loop_Mark p1) (l:1 spt) = ((acc_vars p1 l):1 spt)) /\
    (acc_vars loop_Tick (l:1 spt) = ((l):1 spt)) /\
    (acc_vars loop_Skip (l:1 spt) = ((l):1 spt)) /\
    (acc_vars loop_Fail (l:1 spt) = ((l):1 spt)) /\
    (acc_vars (loop_Raise v) (l:1 spt) = ((l):1 spt)) /\
    (acc_vars (loop_Call ret dest args handler) (l:1 spt) =
           ((match ret with NONE -> l
           | SOME (vs,live) ->
             (let l = list_insert vs l in
               match handler with NONE -> l
               | SOME (n,p1,p2,l1) ->
                   acc_vars p1 (acc_vars p2 (sptree_insert n one
                       l)))):1 spt)) /\
    (acc_vars (loop_LocValue n m) (l:1 spt) = ((sptree_insert n one l):1
    spt)) /\
    (acc_vars (loop_Assign n exp) (l:1 spt) = ((sptree_insert n one l):1
    spt)) /\
    (acc_vars (loop_Primitive lhss pop rhss) (l:1 spt) = ((list_insert lhss
    l):1 spt)) /\
    (acc_vars (loop_ShMem op n exp) (l:1 spt) = ((sptree_insert n one l):1
    spt)) /\
    (acc_vars (loop_Store exp n) (l:1 spt) = ((l):1 spt)) /\
    (acc_vars (loop_SetGlobal w exp) (l:1 spt) = ((l):1 spt)) /\
    (acc_vars (loop_Load32 n m) (l:1 spt) = ((sptree_insert m one l):1 spt)) /\
    (acc_vars (loop_LoadByte n m) (l:1 spt) = ((sptree_insert m one l):1
    spt)) /\
    (acc_vars (loop_Store32 n m) (l:1 spt) = ((l):1 spt)) /\
    (acc_vars (loop_StoreByte n m) (l:1 spt) = ((l):1 spt)) /\
    (acc_vars (loop_FFI name n1 n2 n3 n4 live) (l:1 spt) = ((l):1 spt))`;
   `acc_vars (loop_Return v) (l:1 spt) = ((l):1 spt)`];;

(* and the interface *)
let _ = unhide_overloads ();;
