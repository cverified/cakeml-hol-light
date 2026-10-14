(* ======================================================== *)
(*  word_remove: ported from HOL4's
    compiler/backend/word_removeScript.sml  *)
(* ======================================================== *)

(*
  This simple compiler phase removes `MustTerminate`, which is a
  semantic-device used to help keep the logical clocks in sync in the
  data_to_word correctness proofs.
*)

needs "compiler/backend/wordLang.ml";;

(*Removes MustTerminate*)

let remove_must_terminate_def = cake_define
  `remove_must_terminate prog =
        match prog with
          (wordLang_Seq p0 p1) -> wordLang_Seq (remove_must_terminate
            p0) (remove_must_terminate p1)
        | (wordLang_If cmp r1 ri e2 e3) ->
       wordLang_If cmp r1 ri (remove_must_terminate e2)
         (remove_must_terminate e3)
        | (wordLang_MustTerminate p) -> remove_must_terminate p
        | (wordLang_Call ret dest args h) ->
       let ret = match ret with NONE -> NONE | SOME
         (v,cutset,ret_handler,l1,l2) ->
                             SOME (v,cutset,remove_must_terminate
                               ret_handler,l1,l2) in
       let h = match h with NONE -> NONE | SOME
         (v,wordLang_prog,l1,l2) -> SOME (v,remove_must_terminate
         wordLang_prog,l1,l2) in
         wordLang_Call ret dest args h
        | (wordLang_Loop names body exit_names) ->
       wordLang_Loop names (remove_must_terminate body) exit_names
        | wordLang_prog -> wordLang_prog`;;
