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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "data_simp"
  ["dataLang"];;

let pSeq_def = new_definition
  `pSeq c1 c2 =
     (if c2 = dataLang_Skip then c1 else dataLang_Seq c1 c2)`;;

let simp_def,simp_ind = define_shaped_rec
  "match"
  [`simp c1 c =
        match c1 with
          (dataLang_Skip:dataLang_prog) -> c
        | (dataLang_Return n) -> dataLang_Return n
        | (dataLang_Raise n) -> dataLang_Raise n
        | (dataLang_Seq c1 c2) -> simp c1 (simp c2 c)
        | (dataLang_If n c2 c3) ->
        pSeq (dataLang_If n (simp c2 dataLang_Skip) (simp c3
          dataLang_Skip)) c
        | (dataLang_Call ret dest args (SOME (v,handler))) ->
        pSeq (dataLang_Call ret dest args (SOME (v,simp handler
          dataLang_Skip))) c
        | c1 -> pSeq c1 c`];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
