(* ======================================================== *)
(*  bvl_jump: ported from HOL4's
    compiler/backend/bvl_jumpScript.sml  *)
(* ======================================================== *)

(*
  A function for generating efficient switch-like jumps in BVL.
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;

(* HOL4 bvl_jumpScript.sml:22-30: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let JumpList_def = cake_define_try_tac (fun () ->
  `MEASURE (LENGTH o SND)`)
  CHEAT_TAC
  `(JumpList n xs =
      (let l = LENGTH xs in
        if l = 0 then Op (closLang_IntOp (closLang_Const (&0))) []
          else
        if l = 1 then HD xs else
          let k = l DIV 2 in
          let ys = TAKE k xs in
          let zs = DROP k xs in
          let lt = (if n + l < 1000000 /\ n + k < 1000000 then Op
            (closLang_IntOp (closLang_LessConstSmall (n + k))) [Var 0]
            else Op (closLang_IntOp closLang_Less) [Op (closLang_IntOp
            (closLang_Const (&(n + k)))) []; Var 0]) in
            If lt (JumpList n ys) (JumpList (n + k) zs)))`;;

let jump_def = cake_define
  `bvl_jump_Jump x xs = Let [x] (JumpList 0 xs)`;;
hol4_overload "Jump" "bvl_jump_Jump";;
