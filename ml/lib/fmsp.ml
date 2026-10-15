(* ======================================================== *)
(*  fmsp: ported from HOL4's
    src/transfer/examples/fmspScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/sptree.ml";;
(* HOL4 ancestors outside the port: finite_map transfer pred_set *)

let sp2fm_def = cake_define
  `sp2fm sp = FUN_FMAP (\k. THE (sptree_lookup k sp)) (domain sp)`;;

let fm2sp_def = cake_define
  `fm2sp fm = ITFMAP sptree_insert fm LN`;;
