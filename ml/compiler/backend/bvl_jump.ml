(* ======================================================== *)
(*  bvl_jump: ported from HOL4's
    compiler/backend/bvl_jumpScript.sml  *)
(* ======================================================== *)

(*
  A function for generating efficient switch-like jumps in BVL.
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/closLang.ml";;
needs "lib/comparison.ml";;
needs "semantics/ast.ml";;

(* HOL4 termination: \\ REPEAT STRIP_TAC \\
   Q.ISPEC_THEN`xs`STRIP_ASSUME_TAC SPLIT_LIST \\ FULL_SIMP_TAC
   std_ss [] \\ REPEAT STRIP_TAC \\ fs
   [rich_listTheory.TAKE_LENGTH_APPEND,
   rich_listTheory.DROP_LENGTH_APPEND] \\ rfs [DIV_EQ_X] >>
   full_simp_tac std_ss [GSYM LENGTH_NIL] >> decide_tac *)
let JumpList_def = cake_define_wf
  `MEASURE (LENGTH o SND)`
  `(JumpList n xs =
      (let l = LENGTH xs in
        if l = 0 then Op (IntOp (Const (&0))) [] else
        if l = 1 then HD xs else
          let k = l DIV 2 in
          let ys = TAKE k xs in
          let zs = DROP k xs in
          let lt = (if n + l < 1000000 /\ n + k < 1000000 then Op
            (IntOp (LessConstSmall (n + k))) [Var 0] else Op (IntOp
            Less) [Op (IntOp (Const (&(n + k)))) []; Var 0]) in
            If lt (JumpList n ys) (JumpList (n + k) zs)))`;;

let jump_def = cake_define
  `bvl_jump_Jump x xs = Let [x] (JumpList 0 xs)`;;
hol4_overload "Jump" "bvl_jump_Jump";;
