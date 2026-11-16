(* ======================================================== *)
(*  loop_call: ported from HOL4's
    pancake/loop_callScript.sml
    A definition theory, with 2 definitions and no theorems.  Needed
    by from_pancake32Prog.ml, from_pancake64Prog.ml and
    loop_live.ml.  *)
(* ======================================================== *)

(*
  Call optimisation for loopLang
*)

needs "compiler/backend/backend_common.ml";;
needs "lib/sptree.ml";;
needs "pancake/loopLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "loop_call"
  ["loopLang"];;

let loop_call_is_load_def = new_definition
  `loop_call_is_load x1 =
     match x1 with
       asm_Load -> T
     | asm_Load8 -> T
     | asm_Load16 -> T
     | asm_Load32 -> T
     | _ -> F`;;

let loop_call_comp_def,loop_call_comp_ind = define_guess
  `loop_call_comp l p =
     match p with
       loop_Skip -> (loop_Skip,l)
     | loop_Call ret dest args handler ->
      ((match dest with SOME _ -> loop_Call ret dest args handler
        | NONE -> (
          match args with [] -> loop_Skip
           | _ -> (
             match sptree_lookup (LAST args) l with NONE -> loop_Call ret
               NONE args handler
              | SOME n -> loop_Call ret (SOME n) (BUTLAST args)
                handler))),LN)
     | loop_LocValue n m -> (loop_LocValue n m,sptree_insert n m l)
     | loop_Assign n (loop_Var m) -> (loop_Assign n (loop_Var m),
                              (match (sptree_lookup n l,sptree_lookup m l)
                                with NONE,NONE -> l
                              | SOME _,NONE -> sptree_delete n l
                              | _,SOME loc -> sptree_insert n loc l))
     | loop_Assign n e -> (loop_Assign n e,
                             (match sptree_lookup n l with NONE -> l
                              | _ -> sptree_delete n l))
     | loop_ShMem op n e -> (loop_ShMem op n e,LN)
     | loop_Load32 m n -> (loop_Load32 m n,
                              (match sptree_lookup n l with NONE -> l
                              | _ -> sptree_delete n l))
     | loop_LoadByte m n -> (loop_LoadByte m n,
                              (match sptree_lookup n l with NONE -> l
                              | _ -> sptree_delete n l))
     | loop_Seq p q ->
       let (np,nl) = loop_call_comp l p in let
           (nq,nl) = loop_call_comp nl q in
        (loop_Seq np nq,LN)
     | loop_If c n ri p q ns ->
       let (np,nl) = loop_call_comp l p in let
           (nq,ml) = loop_call_comp l q in
        (loop_If c n ri np nq ns,LN)
     | loop_Loop ns p ms ->
       let (np,nl) = loop_call_comp LN p in
        (loop_Loop ns np ms,LN)
     | loop_Mark p ->
       let (np,nl) = loop_call_comp l p in
        (loop_Mark np,nl)
     | loop_FFI str n m n' m' nl ->
       (loop_FFI str n m n' m' nl,LN)
     | loop_Tick -> (loop_Tick,LN)
     | loop_Raise n -> (loop_Raise n,LN)
     | loop_Return n -> (loop_Return n,LN)
     | loop_Primitive lhss pop rhss ->
      (loop_Primitive lhss pop rhss,list_delete lhss l)
     | loop_Arith arith ->
      (loop_Arith arith,
       (match arith with
         LLongMul r1 r2 r3 r4 ->
           (match (sptree_lookup r1 l,sptree_lookup r2 l) with
              (NONE,NONE) -> l
            | (SOME _,NONE) -> sptree_delete r1 l
            | (NONE,SOME loc) -> sptree_delete r2 l
            | _ -> sptree_delete r1 (sptree_delete r2 l))
       | LLongDiv r1 r2 r3 r4 r5 ->
           (match (sptree_lookup r1 l,sptree_lookup r2 l) with
              (NONE,NONE) -> l
            | (SOME _,NONE) -> sptree_delete r1 l
            | (NONE,SOME loc) -> sptree_delete r2 l
            | _ -> sptree_delete r1 (sptree_delete r2 l))
       | LDiv r1 r2 r3 ->
           (match sptree_lookup r1 l with
              NONE -> l
            | _ -> sptree_delete r1 l)
       | _ -> l))
     | p -> (p,l)`;;


(*
EVAL “comp LN (LocValue 1 3)”;

EVAL “comp LN
       (Seq (LocValue 1 3)
        (Assign 2 (Var 1)))”;

EVAL “comp LN
       (Seq (LocValue 1 3)
        (Seq (Assign 2 (Var 1))
         (Seq (Call NONE NONE [2] NONE) Skip)))”


EVAL “(comp
       (Seq (LocValue 1 3)
        (Seq (Assign 2 (Var 1))
         (Seq (Call NONE NONE [2] NONE) Skip))), s)”

*)

(* and the interface *)
let _ = unhide_overloads ();;
