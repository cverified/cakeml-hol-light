(* ======================================================== *)
(*  word_remove: ported from HOL4's
    compiler/backend/word_removeScript.sml  *)
(* ======================================================== *)

(*
  This simple compiler phase removes `MustTerminate`, which is a
  semantic-device used to help keep the logical clocks in sync in the
  data_to_word correctness proofs.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "semantics/ast.ml";;

(*Removes MustTerminate*)

let remove_must_terminate_def = cake_define
  `remove_must_terminate prog =
        match prog with
          (Seq p0 p1) -> Seq (remove_must_terminate p0)
            (remove_must_terminate p1)
        | (If cmp r1 ri e2 e3) ->
       If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate
         e3)
        | (MustTerminate p) -> remove_must_terminate p
        | (Call ret dest args h) ->
       (let ret = match ret with NONE -> NONE | SOME
         (v,cutset,ret_handler,l1,l2) ->
                             SOME (v,cutset,remove_must_terminate
                               ret_handler,l1,l2) in
       let h = match h with NONE -> NONE | SOME (v,prog,l1,l2) ->
         SOME (v,remove_must_terminate prog,l1,l2) in
         Call ret dest args h)
        | (Loop names body exit_names) ->
       Loop names (remove_must_terminate body) exit_names
        | prog -> prog`;;
