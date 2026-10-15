(* ======================================================== *)
(*  lab_filter: ported from HOL4's
    compiler/backend/lab_filterScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase removes all Skip instructions (generated from
  Tick in stackLang).
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/encoders/asm/asm.ml";;

let not_skip_def = cake_define
  `not_skip l = (match l with Asm (Asmi (Inst Skip)) _1 _2 -> F | _3
  -> T)`;;

let filter_skip_def = cake_define_list
  [`filter_skip [] = []`;
   `filter_skip (Section n xs :: rest) =
         Section n (FILTER not_skip xs) :: filter_skip rest`];;
