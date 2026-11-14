(* ======================================================== *)
(*  data_simp: ported from HOL4's
    compiler/backend/data_simpScript.sml
    A definition theory, with 2 definitions and no theorems.  Needed
    by backend_passes.ml, bvi_to_data.ml, dataSem.ml and
    data_simpProof.ml.  *)
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

needs "compiler/backend/dataLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "data_simp"
  ["dataLang"];;

let pSeq_def = new_definition
  `pSeq c1 c2 =
     if c2 = data_Skip then c1 else data_Seq c1 c2`;;

let simp_def,simp_ind = define_shaped_rec
  "match"
  `simp c1 c =
     match c1 with
       data_Skip -> c
     | data_Return n -> data_Return n
     | data_Raise n -> data_Raise n
     | data_Seq c1 c2 -> simp c1 (simp c2 c)
     | data_If n c2 c3 ->
        pSeq (data_If n (simp c2 data_Skip) (simp c3 data_Skip)) c
     | data_Call ret dest args (SOME (v,handler)) ->
        pSeq (data_Call ret dest args (SOME (v,simp handler data_Skip))) c
     | c1 -> pSeq c1 c`;;

(* and the interface *)
let _ = unhide_overloads ();;
