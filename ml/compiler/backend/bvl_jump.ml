(* ======================================================== *)
(*  bvl_jump: ported from HOL4's
    compiler/backend/bvl_jumpScript.sml
    A definition theory, with 2 definitions and no theorems.  Needed
    by bvl_jumpProof.ml, clos_to_bvl.ml and presLang.ml.  *)
(* ======================================================== *)

(*
  A function for generating efficient switch-like jumps in BVL.
*)

needs "compiler/backend/bvl.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvl_jump"
  ["bvl"];;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 bvl_jumpScript.sml:22-30: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let JumpList_def,JumpList_ind = define_guess_cheat
  [`(JumpList n xs =
      (let l = LENGTH xs in
        if l = 0 then bvl_Op (closLang_IntOp (closLang_Const (&0)))
          [] else
        if l = 1 then HD xs else
          let k = l DIV 2 in
          let ys = TAKE k xs in
          let zs = DROP k xs in
          let lt = (if n + l < 1000000 /\ n + k < 1000000 then
            bvl_Op (closLang_IntOp (closLang_LessConstSmall (n + k)))
            [bvl_Var 0] else bvl_Op (closLang_IntOp closLang_Less)
            [bvl_Op (closLang_IntOp (closLang_Const (&(n + k)))) [];
            bvl_Var 0]) in
            bvl_If lt (JumpList n ys) (JumpList (n + k) zs)))`];;

let jump_def = new_definition
  `bvl_jump_Jump x xs = bvl_Let [x] (JumpList 0 xs)`;;

(* and the interface *)
let _ = unhide_overloads ();;
