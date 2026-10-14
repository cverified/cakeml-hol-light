(* ======================================================== *)
(*  bvl_jump: ported from HOL4's
    compiler/backend/bvl_jumpScript.sml  *)
(* ======================================================== *)

(*
  A function for generating efficient switch-like jumps in BVL.
*)

needs "compiler/backend/bvl.ml";;

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
        if l = 0 then bvl_Op (closLang_IntOp (closLang_Const 0)) []
          else
        if l = 1 then HD xs else
          let k = l DIV 2 in
          let ys = TAKE k xs in
          let zs = DROP k xs in
          let lt = (if n + l < 1000000 /\ n + k < 1000000 then bvl_Op
            (closLang_IntOp (closLang_LessConstSmall (n + k))) [bvl_Var
            0] else bvl_Op (closLang_IntOp (LESS)) [bvl_Op
            (closLang_IntOp (closLang_Const (&(n + k)))) []; bvl_Var 0])
            in
            bvl_If lt (JumpList n ys) (JumpList (n + k) zs)))`;;

let Jump_def = cake_define
  `bvl_jump_Jump x xs = bvl_Let [x] (JumpList 0 xs)`;;
