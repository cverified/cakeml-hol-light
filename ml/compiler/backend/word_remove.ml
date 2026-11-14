(* ======================================================== *)
(*  word_remove: ported from HOL4's
    compiler/backend/word_removeScript.sml
    A definition theory, with 1 definition and 1 theorem.  Needed by
    backend.ml, backend_passes.ml, wordConvsProof.ml,
    word_removeProof.ml, word_to_word.ml and word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  This simple compiler phase removes `MustTerminate`, which is a
  semantic-device used to help keep the logical clocks in sync in the
  data_to_word correctness proofs.
*)

needs "compiler/backend/wordLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_remove"
  ["wordLang"];;

let _ = do_list hide_constant ["pmatch"];;

(*Removes MustTerminate*)

let _ = size_thms "wordLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let remove_must_terminate_def,remove_must_terminate_ind = define_wf
  `MEASURE (\x0. wordLang_prog_size (\x. 0) x0)`
  [`remove_must_terminate prog =
        match prog with
          wordLang_Seq p0 p1 -> wordLang_Seq (remove_must_terminate
            p0) (remove_must_terminate p1)
        | (wordLang_If cmp r1 ri e2 e3) ->
       wordLang_If cmp r1 ri (remove_must_terminate e2)
         (remove_must_terminate e3)
        | (wordLang_MustTerminate p) -> remove_must_terminate p
        | (wordLang_Call ret dest args h) ->
       (let ret = (match ret with NONE -> NONE | SOME
         (v,cutset,ret_handler,l1,l2) ->
                             SOME (v,cutset,remove_must_terminate
                               ret_handler,l1,l2)) in
       let h = (match h with NONE -> NONE | SOME (v,prog,l1,l2) ->
         SOME (v,remove_must_terminate prog,l1,l2)) in
         wordLang_Call ret dest args h)
        | (wordLang_Loop names body exit_names) ->
       wordLang_Loop names (remove_must_terminate body) exit_names
        | prog -> prog`];;

let remove_must_terminate_pmatch = prove
 (`!prog.
   remove_must_terminate prog =
   (match prog with (wordLang_Seq p0 p1) -> wordLang_Seq
     (remove_must_terminate p0) (remove_must_terminate p1) |
     (wordLang_If cmp r1 ri e2 e3) ->
     wordLang_If cmp r1 ri (remove_must_terminate e2)
       (remove_must_terminate e3) | (wordLang_MustTerminate p) ->
       remove_must_terminate p | (wordLang_Call ret dest args h) ->
     (let ret = (match ret with NONE -> NONE | SOME
       (v,cutset,ret_handler,l1,l2) ->
                           SOME (v,cutset,remove_must_terminate
                             ret_handler,l1,l2)) in
     let h = (match h with NONE -> NONE | SOME (v,prog,l1,l2) -> SOME
       (v,remove_must_terminate prog,l1,l2)) in
       wordLang_Call ret dest args h) | (wordLang_Loop names body
         exit_names) ->
     wordLang_Loop names (remove_must_terminate body) exit_names |
       prog -> prog)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
