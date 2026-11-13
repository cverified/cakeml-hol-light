(* ======================================================== *)
(*  fmsp: ported from HOL4's
    src/transfer/examples/fmspScript.sml  *)
(* ======================================================== *)

needs "lib/sptree.ml";;

(* this file is of no theory of the port: the overloads it
   registers are in the scope of every file *)
let _ = hol4_lib ();;
(* HOL4 ancestors outside the port: finite_map transfer pred_set *)

let sp2fm_def = new_definition
  `sp2fm sp = FUN_FMAP (\k. THE (sptree_lookup k sp)) (domain sp)`;;

let fm2sp_def = new_definition
  `fm2sp fm = ITFMAP sptree_insert fm LN`;;
