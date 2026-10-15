(* ======================================================== *)
(*  word_elim: ported from HOL4's
    compiler/backend/word_elimScript.sml  *)
(* ======================================================== *)

(*
  Implementation for wordLang dead-code elimination.

  Analyses code to give a next-step function as a num_set num_map.
  Uses flat_elim functions to close the next-step function and give a
    set of
    reachable functions.
  Removes unreachable functions from the code.
*)

needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;


let find_word_loc_def = cake_define
  `(find_word_loc ((name:num),_1,_2) = name)`;;

let find_word_ref_def = cake_define
  `find_word_ref x1 =
        match x1 with
          wordLang_MustTerminate p -> find_word_ref p
        | (Call ret target _3 handler) -> sptree_union
           (match target with NONE -> LN | SOME n -> (sptree_insert n
             one LN))
               (sptree_union
                   (match ret with NONE -> LN | SOME
                     (_4,_5,ret_handler,l1,_6) ->
                           sptree_insert l1 one (find_word_ref
                             (ret_handler)))
                   (match handler with NONE -> LN | SOME
                     (_7,ex_handler,_8,_9) -> find_word_ref
                     (ex_handler)))
        | (Seq p1 p2) -> sptree_union (find_word_ref p1)
          (find_word_ref p2)
        | (If _10 _11 _12 p1 p2) ->
           sptree_union (find_word_ref p1) (find_word_ref p2)
        | (LocValue _13 n) -> sptree_insert n one LN
        | (Loop names body exit_names) -> find_word_ref body
        | _14 -> LN`;;

(* HOL4 ML code, not ported:
val find_word_ref_ind = theorem "find_word_ref_ind";
*)

let analyse_word_code_def = cake_define_list
  [`analyse_word_code [] = (LN:(1 spt) spt)`;
   `analyse_word_code ((n,args,prog) :: t) =
            sptree_insert n (find_word_ref prog)
              (analyse_word_code t)`];;

let remove_word_code_def = cake_define
  `remove_word_code reachable l =
       FILTER (\x. IS_SOME (sptree_lookup (FST x) reachable)) l`;;

let remove_word_prog_def = cake_define
  `remove_word_prog (n:num) code =
       (let t = analyse_word_code code in
       let reachable = closure_spt (sptree_insert n one (LN:1 spt)) t
         in
       remove_word_code reachable code)`;;
