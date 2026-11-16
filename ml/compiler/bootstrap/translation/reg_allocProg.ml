(* ======================================================== *)
(*  reg_allocProg: ported from HOL4's
    compiler/bootstrap/translation/reg_allocProgScript.sml
    A definition theory, with 1 definition and 3 theorems.  Needed
    by inferProg.ml.  *)
(* ======================================================== *)

(*
  Translate the compiler's register allocator.
*)

needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/proofs/reg_allocProof.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/bootstrap/translation/pancake_parseProg.ml";;
needs "lib/state_transformer.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "reg_allocProg"
  ["basisProg"; "linear_scan"; "ml_monad_translator"; "ml_translator";
   "pancake_parseProg"; "reg_alloc"; "reg_allocProof"];;

(* HOL4 reg_allocProgScript.sml:11-14: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:16-18: code that the source has in a comment *)

(* HOL4 reg_allocProgScript.sml:22-23: ML code, not ported *)
(* HOL4 reg_allocProgScript.sml:24-26: code that the source has in a comment *)

(* HOL4 reg_allocProgScript.sml:33-35: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:37-38: ML code, not ported *)

(*
 *  Set up the monadic translator
 *)

(* The record types used for the monadic state and exceptions *)
(* HOL4 reg_allocProgScript.sml:45-47: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:49-51: ML code, not ported *)

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

(* HOL4 reg_allocProgScript.sml:56-59: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:61-69: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:71-78: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:80-81: ML code, not ported *)

(* Initialization *)

(* HOL4 reg_allocProgScript.sml:85-94: ML code, not ported *)

(*
 * Translate the register allocator
 *)
(* HOL4 reg_allocProgScript.sml:99-102: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:104-115: code that the source has in a
   comment *)

(* HOL4 reg_allocProgScript.sml:117: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:119-120: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:122-126: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:128-134: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:136-139: ML code, not ported *)

(* [local] *)
let rewrite_subs = prove
 (`(st_ex_MAP adj_ls_sub = st_ex_MAP (\v. adj_ls_sub v)) /\
   (st_ex_MAP node_tag_sub = st_ex_MAP (\v. node_tag_sub v)) /\
   (st_ex_PARTITION move_related_sub = st_ex_PARTITION (\v. move_related_sub
     v)) /\
   (st_ex_MAP degrees_sub = st_ex_MAP (\v. degrees_sub v)) /\
   (st_ex_FILTER (considered_var k) xs ys = st_ex_FILTER (\v. considered_var
     k v) xs ys) /\
   (st_ex_MAP (deg_or_inf kk) xs = st_ex_MAP (\x. deg_or_inf kk x) xs)`,
  CHEAT_TAC);;

(* HOL4 reg_allocProgScript.sml:152: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:154: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:156: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:158-159: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:161-163: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:165: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:167: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:174: ML code, not ported *)

(* TODO: something in the monadic translator automatically rewrites
  the ¬ (a ∧ b) check
  and then fails on the original def*)

(* HOL4 reg_allocProgScript.sml:180-181: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:183-188: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:190-192: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:194-198: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:200: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:207-208: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:227-230: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:232-235: ML code, not ported *)

(* Finish the monadic translation *)
(* Rewrite reg_alloc_aux before giving it to the monadic translator *)
(* [local] *)
let reg_alloc_aux_trans_def = prove
 (`!k mtable ct forced fs x.
      reg_alloc_aux alg scost k mtable ct forced fs x =
      run_ira_state (do_reg_alloc alg scost k mtable ct forced fs x)
        (mk_ra_state (SND (SND x),[]) (SND (SND x),Atemp) (SND (SND x),0)
          (SND (SND x)) [] [] [] [] [] (SND (SND x),0) (SND (SND x),F) [])`,
  CHEAT_TAC);;

(* HOL4 reg_allocProgScript.sml:259-260: ML code, not ported *)

(* The final function used by the compiler *)
(* HOL4 reg_allocProgScript.sml:263: ML code, not ported *)


(* === Translation of linear scan register allocator === *)

(* HOL4 reg_allocProgScript.sml:268: ML code, not ported *)

(*
 *  Set up the monadic translator
 *)


(* The record types used for the monadic state and exceptions *)
(* HOL4 reg_allocProgScript.sml:276-277: ML code, not ported *)
(* HOL4 reg_allocProgScript.sml:278: code that the source has in a comment *)

(* HOL4 reg_allocProgScript.sml:280-282: ML code, not ported *)

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

(* HOL4 reg_allocProgScript.sml:287-290: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:292-300: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:302-303: ML code, not ported *)

(* Initialization *)

(* HOL4 reg_allocProgScript.sml:307-316: ML code, not ported *)

(* Translate basics *)

(* HOL4 reg_allocProgScript.sml:320-325: ML code, not ported *)

(* Translate linear scan register allocator *)

let map_colors_sub_def,map_colors_sub_ind = define_guess
  `(map_colors_sub [] = st_ex_return []) /\
   (map_colors_sub (CONS x xs) =
         st_ex_bind (colors_sub x)
           (\fx. st_ex_bind (map_colors_sub xs)
                   (\fxs. st_ex_return (CONS fx fxs))))`;;

let map_colors_sub_eq = prove
 (`map_colors_sub = st_ex_MAP colors_sub`,
  CHEAT_TAC);;

(* HOL4 reg_allocProgScript.sml:344-348: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:350-364: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:366-367: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:369: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:371-372: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:374-376: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:378-381: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:383-384: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:386: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:388-391: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:393-398: ML code, not ported *)

(* HOL4 reg_allocProgScript.sml:400-410: ML code, not ported *)


(* HOL4 reg_allocProgScript.sml:413-448: code that the source has in a
   comment *)

(* HOL4 reg_allocProgScript.sml:450: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
