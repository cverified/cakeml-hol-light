(* ======================================================== *)
(*  mc_multiword: ported from HOL4's
    examples/machine-code/multiword/mc_multiwordScript.sml  *)
(*  Of this HOL4 library theory only the definitions that the
    CakeML port needs are ported.  *)
(* ======================================================== *)

needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
(* HOL4 ancestors outside the port: words address arithmetic list
   address pair rich_list integer *)

let single_add_word_def = cake_define
  `single_add_word w1 w2 c =
     (let (z,c) = single_add w1 w2 (~(c = ((n2w 0):'a word))) in
       ((z:'a word),((b2w c):'a word)))`;;

let single_sub_word_def = cake_define
  `single_sub_word w1 w2 c =
     (let (z,c) = single_sub w1 w2 (~(c = ((n2w 0):'a word))) in
       ((z:'a word),((b2w c):'a word)))`;;

let single_div_pre_def = cake_define
  `single_div_pre r2 r0 r9 <=> ~(
     r9 = ((n2w 0x0):'a word)) /\
     (w2n r2 * dimword (:'a) + w2n r0) DIV w2n r9 < dimword (:'a)`;;
