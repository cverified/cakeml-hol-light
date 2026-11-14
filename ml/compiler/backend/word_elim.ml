(* ======================================================== *)
(*  word_elim: ported from HOL4's
    compiler/backend/word_elimScript.sml
    A definition theory, with 5 definitions and no theorems.  Needed
    by wordConvsProof.ml, word_elimProof.ml and
    word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Implementation for wordLang dead-code elimination.

  Analyses code to give a next-step function as a num_set num_map.
  Uses flat_elim functions to close the next-step function and give a set of
    reachable functions.
  Removes unreachable functions from the code.
*)

needs "compiler/backend/wordLang.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_elim"
  ["wordLang"];;


let find_word_loc_def = new_definition
  `(find_word_loc ((name:num),_,_) = name)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let find_word_ref_def,find_word_ref_ind = define_wf
  `MEASURE (\x0. word_prog_size (\x. 0) x0)`
  `find_word_ref x1 =
     match x1 with
       word_MustTerminate p -> find_word_ref p
     | word_Call ret target _ handler -> sptree_union
           (match target with NONE -> LN | SOME n -> (sptree_insert n one
             LN))
               (sptree_union
                   (match ret with NONE -> LN
                       | SOME (_,_,ret_handler,l1,_) ->
                           sptree_insert l1 one (find_word_ref
                             (ret_handler)))
                   (match handler with NONE -> LN
                       | SOME (_,ex_handler,_,_) -> find_word_ref
                         (ex_handler)))
     | word_Seq p1 p2 -> sptree_union (find_word_ref p1) (find_word_ref p2)
     | word_If _ _ _ p1 p2 ->
           sptree_union (find_word_ref p1) (find_word_ref p2)
     | word_LocValue _ n -> sptree_insert n one LN
     | word_Loop names body exit_names -> find_word_ref body
     | _ -> LN`;;

(* HOL4 word_elimScript.sml:41: ML code, not ported *)

let analyse_word_code_def,analyse_word_code_ind = define_rec
  `(analyse_word_code [] = (LN:(1 spt) spt)) /\
   (analyse_word_code (CONS (n,args,prog) t) =
            ((sptree_insert n (find_word_ref prog) (analyse_word_code
                t)):(1 spt) spt))`;;

let remove_word_code_def = new_definition
  `remove_word_code reachable l =
       FILTER (\x. IS_SOME (sptree_lookup (FST x) reachable)) l`;;

let remove_word_prog_def = new_definition
  `remove_word_prog (n:num) code =
       let t = analyse_word_code code in
       let reachable = closure_spt (sptree_insert n one (LN:1 spt)) t in
       remove_word_code reachable code`;;

(* and the interface *)
let _ = unhide_overloads ();;
