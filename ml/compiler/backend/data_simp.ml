(* ======================================================== *)
(*  data_simp: ported from HOL4's
    compiler/backend/data_simpScript.sml  *)
(* ======================================================== *)

(*
  This simple compiler phase cleans up dataLang programs.  The simp
  optimisation removes Skips and deletes some dead code created by
  Raise and Return.

  Example:

    Seq (Seq Skip (Raise n)) anything_here

  translates into

    Raise n

  It also right-associates Seq, e.g.

    Seq (Seq x1 x2) x3 --> Seq x1 (Seq x2 x3)
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "semantics/ast.ml";;

let pSeq_def = cake_define
  `pSeq c1 c2 =
     (if c2 = Skip then c1 else Seq c1 c2)`;;

let simp_def = cake_define
  `simp c1 c =
        match c1 with
          Skip -> c
        | (Return n) -> Return n
        | (Raise n) -> Raise n
        | (Seq c1 c2) -> simp c1 (simp c2 c)
        | (If n c2 c3) ->
        pSeq (If n (simp c2 Skip) (simp c3 Skip)) c
        | (Call ret dest args (SOME (v,handler))) ->
        pSeq (Call ret dest args (SOME (v,simp handler Skip))) c
        | c1 -> pSeq c1 c`;;
